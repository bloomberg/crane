(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** {1 Loopify Pass: Recursive-to-Iterative Transformation}

    Transforms recursive MiniCpp functions and methods into iterative equivalents
    using while loops and explicit stacks. This eliminates C++ stack recursion,
    enabling safe execution of deeply recursive algorithms extracted from Coq.

    {2 Motivation}

    Coq programs often use deep recursion (e.g., structural recursion on large
    trees or lists). Direct translation to C++ would cause stack overflow on
    large inputs. The loopify pass converts recursion into iteration, using:
    - Shadow variables for tail recursion
    - Explicit [std::vector] stacks for non-tail recursion
    - Typed frame structs with [std::variant] dispatching

    {2 Supported Recursion Patterns}

    {3 Tail Recursion}
    [f x = if base(x) then result else f(next(x))]

    Converted to [while] loop with mutable shadow variables. No stack needed
    since no work happens after the recursive call.

    {3 Non-Tail Recursion (Single Call)}
    [f x = if base(x) then result else combine(x, f(next(x)))]

    Uses explicit stack with [CraneEnter] and [_Call] frames. The [CraneEnter] frame
    initiates computation; [_Call] frames save continuation context.

    {3 Multi-Recursion (2+ Calls per Branch)}
    [fib n = if n < 2 then 1 else fib(n-1) + fib(n-2)]

    Uses chained [_Call] frames or [CraneEnter/_After/_Combine] pattern to handle
    multiple recursive calls in the same expression.

    {2 Architecture}

    The pass operates in several stages:

    1. {b Classification}: Analyze function body to determine recursion kind
       (tail, non-tail, multi-call) via {!classify}

    2. {b Transformation}: Apply appropriate strategy:
       - {!transform_tail} for tail recursion → while loop with shadow vars
       - {!transform_nontail} for non-tail → frame-based stack

    3. {b Normalized input}: {!Normalize} binds every non-tail recursive call
       in evaluation order before translation, so the transforms meet each
       one as a statement; tail modulo cons reads the body with those
       bindings put back ({!Cpp_temporaries.own_stmts})

    4. {b Frame Generation}: Create typed frame structs ([CraneEnter], [_ResumeN],
       etc.) and a dispatch loop that tests the popped frame with
       [std::holds_alternative] in an if/else-if chain

    {2 Decltype Rewriting}

    Frame struct fields with unknown types fall back to [decltype(expr)].  If
    [expr] references lambda-scoped variables that are not in scope at the
    struct definition level, the C++ will fail to compile.  The function
    {!rewrite_field_access_for_decltype} rewrites both plain variable
    references and field accesses to [std::declval<T&>()] forms, making the
    [decltype] expression valid at struct scope.

    {2 Adopted Bodies}

    Some of a function's recursion lives in a lambda: a fixpoint local to it
    (Coq's [let fix], or a [fix] applied in argument position), or a
    mutual-recursion partner that inlining left as an immediately-invoked
    lambda.  Such a body is not loopified on its own: two machines cannot share
    a stack, so each would unwind through the other and the C++ would still
    recurse.  Instead it is {e adopted} as a second entry point of the
    enclosing machine -- its own [CraneEnter_<name>] frame carrying its parameters
    and the variables it captures, dispatched from the same loop over the same
    [std::variant] stack.  See {!adopted} for how the two shapes are made
    alike, {!find_in_flow} for which statements are searched, and
    {!machine_entry} for what an entry is.

    {2 Modules}

    The pass is split by responsibility: {!Loopify_analysis} finds and
    classifies recursive calls, {!Loopify_tail}, {!Loopify_tmc} and
    {!Loopify_frame} are the rewrite strategies, and this module dispatches
    between them, inlines mutual recursion, and walks declarations.

    {2 Entry Points}

    - {!transform_fundef}: Transform a top-level function definition
    - {!transform_method}: Transform a struct method
    - {!loopify_decl}: Main dispatch for all declaration types

    @since Crane 1.0 *)

open Names
open Minicpp

include Loopify_analysis
include Loopify_tail
include Loopify_tmc
include Loopify_frame

(** {2 Main transformation dispatch} *)

(** Check if a function body contains any call to a function identified by
    [target_id]. Searches through all statements and nested expressions for a
    [CPPfun_call (call_opaque, CPPvar id, of_reversed (_))] where [id] equals [target_id].

    @param target_id The function name to search for
    @param stmts     The statement list (function body) to search
    @return [true] if any call to [target_id] is found *)
let body_calls_id target_id stmts =
  body_exists
    (function
      | CPPfun_call (_, CPPvar id, _) when Id.equal id target_id -> true
      | _ -> false )
    stmts

(** {3 GlobRef-based mutual recursion} *)

(** Check if a function body calls any function whose [GlobRef.t] appears in
    [refs]. Searches through all statements and nested expressions for a
    [CPPfun_call (call_opaque, CPPglob (r, _, _), of_reversed (_))] where [r] matches any element of [refs].

    Used in mutual recursion detection to determine whether a callee calls back
    into the current function.

    @param refs List of [GlobRef.t] values to check for
    @param body The statement list (function body) to search
    @return [true] if any call to a ref in [refs] is found *)
let body_calls_any_ref refs body =
  let eq r sr = Common.globref_equal r sr in
  let label_of = function
    | GlobRef.ConstRef c -> Some (Label.to_id (Constant.label c))
    | GlobRef.VarRef v -> Some v
    | _ -> None
  in
  body_exists
    (function
      | CPPfun_call (_, CPPglob (r, _, _), _) when List.exists (eq r) refs -> true
      | CPPfun_call (_, CPPvar id, _) ->
        List.exists
          (fun r ->
            match label_of r with
            | Some label -> Id.equal id label
            | None -> false )
          refs
      | _ -> false )
    body

(** {3 Generic mutual recursion inlining}

    Both the GlobRef-based path ({!try_inline_mutual_into}) and the
    Id-based path ({!try_inline_mutual_fields}) perform the same core
    operation: find every call to a target function and replace it with
    the callee's body.  This record and the three generic traversal
    functions capture that shared logic, parameterised only by how the
    call target is recognised. *)

(** Parameters for a single inlining substitution. *)
type inline_spec = {
  is_target : cpp_expr -> bool;
      (** [true] if [expr] is a call to the function being inlined *)
  get_args : cpp_expr -> cpp_expr list;
      (** Extract the argument list from a target call expression *)
  params : (Id.t * cpp_type) list;
      (** Formal parameters of the function being inlined (possibly renamed) *)
  body : cpp_stmt list;
      (** Body of the function being inlined (possibly with renamed variables) *)
  ret_ty : cpp_type;
      (** Return type of the function being inlined.  A non-tail call becomes
          a lambda around [body]; this is that lambda's return type. *)
}

(** Inline all calls matching [spec] in a statement list.  Tail calls are
    expanded to parameter bindings plus body; non-tail calls become IIFEs.
    {!generic_inline_stmt} handles individual statements; this is just
    [concat_map]. *)
let rec generic_inline_stmts spec stmts =
  List.concat_map (generic_inline_stmt spec) stmts

(** Inline all calls matching [spec] in a single statement. *)
and generic_inline_stmt spec = function
  | Sreturn (Some e) when spec.is_target e ->
    (* Tail call — substitute parameters and splice body inline *)
    let bindings =
      List.map2
        (fun (pid, ty) arg -> Sasgn (pid, Declare ty, arg))
        spec.params (spec.get_args e)
    in
    bindings @ spec.body
  | Sif (cond, then_br, else_br) ->
    [Sif (cond,
          generic_inline_stmts spec then_br,
          generic_inline_stmts spec else_br)]
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    [ Scustom_case
        ( ty, generic_inline_expr spec scrut, tyargs,
          List.map (fun (ps, rty, b) ->
            (ps, rty, generic_inline_stmts spec b)) branches,
          err ) ]
  | Sreturn (Some e) -> [Sreturn (Some (generic_inline_expr spec e))]
  | Sasgn (id, ty, e) -> [Sasgn (id, ty, generic_inline_expr spec e)]
  | Sassign_expr (lhs, e) ->
    [Sassign_expr (generic_inline_expr spec lhs, generic_inline_expr spec e)]
  | Sexpr e -> [Sexpr (generic_inline_expr spec e)]
  | Smatch (scrut, branches, default) ->
    [ Smatch
        ( scrut,
          List.map (fun br ->
            { br with smb_body = generic_inline_stmts spec br.smb_body })
            branches,
          Option.map (generic_inline_stmts spec) default ) ]
  | Sblock ss -> [Sblock (generic_inline_stmts spec ss)]
  | s -> [s]

(** Inline all calls matching [spec] in an expression.  Non-tail calls are
    wrapped in an immediately-invoked lambda (IIFE). *)
and generic_inline_expr spec expr =
  if spec.is_target expr then
    (* Non-tail call — wrap inlined body in immediately-invoked lambda *)
    let lparams =
      List.map (fun (pid, ty) -> (ty, Some pid)) spec.params
    in
    CPPfun_call
      ( call_opaque,
        CPPlambda
          { cl_params = of_reversed lparams;
            cl_tparams = [];
            cl_ret = Some spec.ret_ty;
            cl_body = spec.body;
            cl_capture = Closure },
        of_reversed (spec.get_args expr) )
  else
    match expr with
    (* A call inside a closure cannot join the loop machine: the closure may
       run after this function returns, or elsewhere.  Inlining there would
       only hand the machine a call it cannot reach. *)
    | CPPlambda _ -> expr
    | _ ->
    map_expr
      (generic_inline_expr spec)
      (fun s ->
        match generic_inline_stmt spec s with
        | [s'] -> s'
        | ss -> Sblock ss )
      Fun.id
      expr

(** Try to inline a mutual recursion partner into a function body.

    Scans [body] for calls to functions registered in {!mutual_fn_table} that
    also call back into the current function (true mutual recursion). If such a
    callee is found, its body is inlined at each call site:

    - {b Tail calls} ([return callee(args)]) are replaced by parameter bindings
      followed by the callee's body directly.
    - {b Non-tail calls} ([let x = callee(args) in ...]) are wrapped in an
      immediately-invoked lambda (IIFE) so the callee's body can use [return].

    Parameter names in the inlined body are prefixed with [_inl_] to avoid
    collisions with the outer function's variables. After inlining, the function
    becomes self-recursive (the callee's calls back to the current function are
    now direct self-calls) and can be loopified by {!transform_fundef}.

    Only the first mutual partner found is inlined (at most one level).

    @param names List of [(GlobRef.t, Id.t)] pairs identifying the current
                 function (used to skip self-calls and detect back-calls)
    @param body  The function body to transform
    @return The body with mutual calls inlined, or the original body if no
            mutual partner was found *)
let try_inline_mutual_into names body =
  (* For each ref this function is known by, skip it (self-call). For each call
     in the body, check if the callee is registered AND lies on a recursion
     cycle back to this function.  A directly-mutual partner (2-way) calls this
     function outright; a longer cycle (e.g. 3-way [a -> b -> c -> a]) reaches
     it only transitively, so we test transitive reachability through the
     registered call graph and inline the whole cycle one hop at a time. *)
  let self_refs = List.map fst names in
  let is_self r = List.exists (Common.globref_equal r) self_refs in
  (* Does [b] call the registered function [r]?  By its global: a local of
     the same name is not the function. *)
  let body_calls_reg r b = body_calls_any_ref [r] b in
  (* Can [start]'s body reach one of [self_refs] through the registered call
     graph (so that inlining [start] moves this function towards
     self-recursion)?  Cycles are broken with a visited set. *)
  let reaches_self start =
    let visited = ref [] in
    let rec go r =
      if List.exists (Common.globref_equal r) !visited then false
      else begin
        visited := r :: !visited;
        match Hashtbl.find_opt mutual_fn_table r with
        | None -> false
        | Some {rf_body = b; _} ->
          body_calls_any_ref self_refs b
          || Hashtbl.fold
               (fun r2 _ acc ->
                 acc
                 || ((not (is_self r2)) && body_calls_reg r2 b && go r2) )
               mutual_fn_table false
      end
    in
    go start
  in
  (* Whether a callee is a registered function on a cycle. *)
  let find_registered_callee_by_ref r =
    if is_self r then None
    else
      match Hashtbl.find_opt mutual_fn_table r with
      | Some {rf_ret_ty; rf_params; rf_body} when reaches_self r ->
        Some (r, rf_ret_ty, rf_params, rf_body)
      | _ -> None
  in
  let rec find_callee_in_expr expr =
    match expr with
    | CPPfun_call (_, CPPglob (r, _, _), _) ->
      ( match find_registered_callee_by_ref r with
      | Some _ as result -> result
      | None -> None )
    | CPPfun_call (_, _, args) ->
      List.find_map find_callee_in_expr (to_reversed args)
    | CPPbinop (_, e1, e2) ->
      ( match find_callee_in_expr e1 with
      | Some _ as r -> r
      | None -> find_callee_in_expr e2 )
    | CPPmove e | CPPderef e | CPPnamespace (_, e) -> find_callee_in_expr e
    | CPPlambda {cl_body = stmts; _} -> find_callee_in_stmts stmts
    | _ -> None
  and find_callee_in_stmts stmts = List.find_map find_callee_in_stmt stmts
  and find_callee_in_stmt = function
    | Sreturn (Some e) -> find_callee_in_expr e
    | Sasgn (_, _, e) | Sexpr e -> find_callee_in_expr e
    | Sif (_, t, e) ->
      ( match find_callee_in_stmts t with
      | Some _ as r -> r
      | None -> find_callee_in_stmts e )
    | Scustom_case (_, scrut, _, branches, _) ->
      ( match find_callee_in_expr scrut with
      | Some _ as r -> r
      | None -> List.find_map (fun (_, _, b) -> find_callee_in_stmts b) branches
      )
    | Smatch (scrut, branches, default) ->
      ( match List.find_map (fun br -> find_callee_in_stmts br.smb_body) branches with
      | Some _ as r -> r
      | None -> match default with Some ss -> find_callee_in_stmts ss | None -> None )
    | Sblock ss -> find_callee_in_stmts ss
    | _ -> None
  in
  (* Inline one cycle partner ([callee_ref]) into [body], returning the new
     body.  Applied repeatedly by the loop below until this function only calls
     itself (or no cycle partner remains). *)
  let inline_one (callee_ref, callee_ret_ty, callee_params, callee_body) body =
    (* Collect all locally-declared IDs from a statement list, including
       structured binding names from Smatch branches. *)
    let rec collect_local_ids stmts =
      List.concat_map collect_local_ids_stmt stmts
    and collect_local_ids_stmt = function
      | Sdecl (id, _) | Sdecl_init (id, _) -> [id]
      | Sasgn (id, Declare _, _) -> [id]
      | Sbind (ids, _) -> ids
      | Smatch (scrut, branches, default) ->
        List.concat_map (fun br ->
          let var_ids = match br.smb_var with Some id -> [id] | None -> [] in
          let field_ids = List.map (fun (id, _, _) -> id) br.smb_field_bindings in
          var_ids @ field_ids @ collect_local_ids br.smb_body
        ) branches
        @ (match default with Some ss -> collect_local_ids ss | None -> [])
      | Sif (_, then_br, else_br) ->
        collect_local_ids then_br @ collect_local_ids else_br
      | Sblock ss -> collect_local_ids ss
      | Swhile (_, ss) -> collect_local_ids ss
      | _ -> []
    in
    (* Generate fresh names for parameters AND all local variables to avoid
       collision with the outer function's bindings. *)
    let param_rename_map =
      List.map
        (fun (pid, _ty) -> (pid, Generated_name.prefixed "_inl" pid))
        callee_params
    in
    let local_ids = collect_local_ids callee_body in
    let local_rename_map =
      List.filter_map (fun id ->
        if List.mem_assoc id param_rename_map then None
        else Some (id, Generated_name.prefixed "_inl" id))
        local_ids
    in
    let rename_map = param_rename_map @ local_rename_map in
    (* The body is inlined as a lambda invoked in place, and a lambda is not
       under the callee's template header: a forwarding parameter [F1 &&f]
       there names the caller's [F1], if anything, and is not forwarding --
       it is an rvalue or an lvalue reference by what that [F1] was deduced
       as, and binds one kind of argument only.  [auto &&] is the forwarding
       reference a lambda can declare. *)
    let fresh_params =
      List.map
        (fun (pid, ty) ->
          let ty =
            match ty with
            | Tref (Forwarding, Tvar _) -> Tref (Forwarding, Tauto)
            | ty -> ty
          in
          (List.assoc pid rename_map, ty))
        callee_params
    in
    (* Rename variables in the callee body *)
    let rename_var id =
      match List.assoc_opt id rename_map with
      | Some fresh -> fresh
      | None -> id
    in
    let rec rename_expr = function
      | CPPvar id -> CPPvar (rename_var id)
      | e -> map_expr rename_expr rename_stmt Fun.id e
    and rename_stmt s =
      match s with
      | Sasgn (id, ty, e) -> Sasgn (rename_var id, ty, rename_expr e)
      | Sdecl (id, ty) -> Sdecl (rename_var id, ty)
      | Smatch (scrut, branches, default) ->
        Smatch (
          { scrut with sc_expr = rename_expr scrut.sc_expr },
          List.map (fun br ->
            { smb_ctor_type = br.smb_ctor_type;
              smb_var = Option.map rename_var br.smb_var;
              smb_field_bindings =
                List.map (fun (id, ty, u) -> (rename_var id, ty, u))
                  br.smb_field_bindings;
              smb_extra_conds = List.map rename_expr br.smb_extra_conds;
              smb_body = List.map rename_stmt br.smb_body })
            branches,
          Option.map (List.map rename_stmt) default)
      | _ -> map_stmt rename_expr rename_stmt Fun.id s
    in
    let fresh_body = List.map rename_stmt callee_body in
    (* Inline: replace calls to callee_ref with fresh_body *)
    let callee_label =
      match callee_ref with
      | GlobRef.ConstRef c -> Label.to_id (Constant.label c)
      | GlobRef.VarRef v -> v
      | _ -> Id.of_string ""
    in
    let is_callee_call = function
      | CPPfun_call (_, CPPglob (r, _, _), _)
        when Common.globref_equal r callee_ref -> true
      | CPPfun_call (_, CPPvar id, _) when Id.equal id callee_label -> true
      | _ -> false
    in
    let get_call_args = function
      | CPPfun_call (_, _, args) -> to_reversed args
      | _ -> []
    in
    let spec = {
      is_target = is_callee_call;
      get_args = get_call_args;
      params = fresh_params;
      body = fresh_body;
      ret_ty = callee_ret_ty;
    } in
    generic_inline_stmts spec body
  in
  (* Inline cycle partners one hop at a time until self-recursive.  Bounded by
     the number of registered functions to guarantee termination. *)
  let rec loop body iters =
    if iters <= 0 then body
    else
      match find_callee_in_stmts body with
      | None -> body
      | Some callee -> loop (inline_one callee body) (iters - 1)
  in
  loop body (Hashtbl.length mutual_fn_table + 1)

(** {2 Inner lambda loopification}

    Transforms self-recursive [std::function] lambdas within function bodies
    into iterative versions using the same while-loop or stack-frame techniques
    as top-level functions. *)

(** Create a {!call_checker} that recognises self-recursive calls within an
    inner lambda. Matches [CPPfun_call (call_opaque, CPPvar id, of_reversed (args))] where [id] equals
    [lambda_name]. All matched calls are marked as non-tail since inner lambda
    calls are processed within expression contexts.

    @param lambda_name The [Id.t] name of the lambda variable (e.g., the [id]
                       in [std::function<...> id = ...])
    @return A {!call_checker} suitable for {!classify}, {!transform_tail}, etc. *)
let lambda_checker (lambda_name : Id.t) : call_checker =
 fun e ->
   match e with
   | CPPfun_call (_, CPPvar id, args) when Id.equal id lambda_name ->
     (* Direct call: [f(args)] — by-reference fixpoint pattern *)
     Some (mk_call_site (to_reversed args))
   | CPPfun_call (_, CPPderef (CPPvar id), args) when Id.equal id lambda_name ->
     (* Dereferenced call — shared_ptr fixpoint pattern *)
     Some (mk_call_site (to_reversed args))
   | _ -> None

(** Walk through a statement list and loopify any self-recursive [std::function]
    lambda assignments.

    Recognises two patterns for self-recursive lambdas:
    + [Sdecl(id, Tfun _); Sasgn(id, Existing, CPPlambda(...))] -- declaration
      followed by assignment (common when Coq's [let fix] is extracted).
    + [Sasgn(id, Some(Tfun _), CPPlambda(...))] -- combined declaration and
      assignment.

    For each matched lambda whose body contains recursive calls to [id] (as
    determined by {!lambda_checker} and {!classify}), applies the appropriate
    transformation ({!transform_tail} or {!transform_nontail}). Lambdas without self-recursion are left unchanged but
    their bodies are recursively scanned for nested lambdas.

    Also descends into all nested statement structures (if/else, while loops,
    match branches, switch, blocks) and into lambda expressions within
    assignments and returns, to find recursive lambda patterns at any depth.

    @param tparams  Type parameters of the enclosing function
    @param body     The statement list to scan and transform
    @return The statement list with all self-recursive inner lambdas loopified *)
let loopify_inner_lambdas ~tparams ?(outer_env = []) body =
  (* What the enclosing scope binds, which a local fixpoint captures. *)
  let outer_env = collect_type_env body @ outer_env in
  let try_loopify_lambda id lparams ret_ty_opt lbody cap =
    let lparams = to_reversed lparams in
    let check = lambda_checker id in
    let lbody = expose_tail_calls check lbody in
    match classify check lbody with
    | No_recursion -> None
    | (Tail_recursion | Nontail_recursion) as kind ->
      let params =
        List.filter_map
          (fun (ty, id_opt) ->
            match id_opt with
            | Some pid -> Some (pid, ty)
            | None -> None )
          lparams
      in
      let ret_ty =
        match ret_ty_opt with
        | Some ty -> ty
        | None -> Tvoid
      in
      let name = Id.to_string id in
      let lbody' =
        match kind with
        | Tail_recursion ->
          report_outcome ~name ~check ~strategy:Lp_tail
            (transform_tail tparams check params ret_ty lbody)
        | Nontail_recursion ->
          report_outcome ~name ~check ~strategy:Lp_frame
            (transform_nontail ~fn_name:name ~outer_env check tparams params
               ret_ty lbody)
        | No_recursion -> CErrors.anomaly (Pp.str "loopify: No_recursion cannot appear here")
      in
      Some lbody'
  in
  (* Y-combinator idiom emitted by {!Translation.gen_local_fix_by_ref} for
     local fixpoints:
     {v
       auto f_impl = [&](A... args, auto& _self_f) { ... _self_f(newargs, _self_f) ... };
       auto f      = [&](A... args) { return f_impl(args, f_impl); };
     v}
     The lambda's LAST parameter is a single self-reference [_self_f] and the
     recursive call forwards it as its own last argument.  The patterns above
     miss this shape: they key on the lambda's own name and on [Tfun] /
     [mk_shared] init exprs, whereas this is [Some Tauto] + [CPPlambda] and
     recurses through the self-parameter.  Recognise it here and, for tail
     recursion, reuse {!transform_tail} with a checker keyed on the self-param
     (dropping the trailing self-forward argument so the remaining args align
     positionally with the non-self loop params).  After transformation the
     self-parameter is unreferenced; the {!Cpp_print} lambda printer emits
     unreferenced params without a name, so there is no [-Wunused-parameter].
     Only single (non-mutual) fixpoints are handled; mutual ones (multiple
     self-params) and non-tail recursion are left unchanged. *)
  let try_loopify_ycomb lparams ret_ty_opt lbody =
    match ycomb_self_id lparams with
    | None -> None
    | Some self_id -> (
      let check = self_checker self_id in
      let lbody = expose_tail_calls check lbody in
      match classify check lbody with
      | No_recursion -> None
      | (Tail_recursion | Nontail_recursion) as kind ->
        (* Loop params = all params except the trailing self-param. *)
        let loop_lparams =
          match List.rev lparams with _ :: rest -> List.rev rest | [] -> []
        in
        let params =
          List.filter_map
            (fun (ty, id_opt) ->
              match id_opt with Some pid -> Some (pid, ty) | None -> None )
            loop_lparams
        in
        let ret_ty = match ret_ty_opt with Some ty -> ty | None -> Tvoid in
        (* The fixpoint's own name, recovered from its self-parameter, so the
           frame structs a non-tail transform emits are named after it. *)
        let name =
          let s = Id.to_string self_id in
          String.sub s
            (String.length self_param_prefix)
            (String.length s - String.length self_param_prefix)
        in
        let body' =
          match kind with
          | Tail_recursion ->
            report_outcome ~name ~check ~strategy:Lp_tail
              (transform_tail tparams check params ret_ty lbody)
          | Nontail_recursion ->
            report_outcome ~name ~check ~strategy:Lp_frame
              (transform_nontail ~fn_name:name ~outer_env check tparams params
                 ret_ty lbody)
          | No_recursion ->
            CErrors.anomaly (Pp.str "loopify: No_recursion cannot appear here")
        in
        (* Params the loop body no longer mentions keep their names here; the
           lambda printer drops the name of any param its body does not
           reference, so unused ones do not trip [-Wunused-parameter]. *)
        Some (lparams, body') )
  in
  let rec process_stmts stmts =
    match stmts with
    | [] -> []
    (* Pattern 1: Sdecl(id, Tfun _) followed by Sasgn(id, Existing,
       CPPlambda(...)) *)
    | Sdecl (id, (Tfun _ as decl_ty))
      :: Sasgn (id2, Existing, CPPlambda
        { cl_params = lparams;
          cl_ret = ret_ty_opt;
          cl_body = lbody;
          cl_capture = cap })
      :: rest
      when Id.equal id id2 ->
      ( match try_loopify_lambda id lparams ret_ty_opt lbody cap with
      | Some lbody' ->
        Sdecl (id, decl_ty)
        :: Sasgn (id, Existing, CPPlambda
          { cl_params = lparams;
          cl_tparams = [];
            cl_ret = ret_ty_opt;
            cl_body = lbody';
            cl_capture = cap })
        :: process_stmts rest
      | None ->
        let lbody' = process_stmts lbody in
        Sdecl (id, decl_ty)
        :: Sasgn (id, Existing, CPPlambda
          { cl_params = lparams;
          cl_tparams = [];
            cl_ret = ret_ty_opt;
            cl_body = lbody';
            cl_capture = cap })
        :: process_stmts rest )
    (* Pattern 2: Sasgn(id, Some(Tfun _), CPPlambda(...)) — combined
       decl+assign *)
    | Sasgn
        ( id,
          (Declare (Tfun _) as tgt),
          CPPlambda
            { cl_params = lparams;
              cl_ret = ret_ty_opt;
              cl_body = lbody;
              cl_capture = cap } )
      :: rest ->
      ( match try_loopify_lambda id lparams ret_ty_opt lbody cap with
      | Some lbody' ->
        Sasgn (id, tgt, CPPlambda
          { cl_params = lparams;
          cl_tparams = [];
            cl_ret = ret_ty_opt;
            cl_body = lbody';
            cl_capture = cap })
        :: process_stmts rest
      | None ->
        let lbody' = process_stmts lbody in
        Sasgn (id, tgt, CPPlambda
          { cl_params = lparams;
          cl_tparams = [];
            cl_ret = ret_ty_opt;
            cl_body = lbody';
            cl_capture = cap })
        :: process_stmts rest )
    (* Pattern 3: shared_ptr fixpoint.

       Matches the two-statement pattern emitted by
       {!Translation.gen_local_fix_shared_ptr}:
       {v
         auto f = make_shared<function<R(A...)>>();
         *f = [=](A... args) mutable { ... };
       v}

       If loopification succeeds (the recursion is converted to a loop),
       the shared_ptr indirection is no longer needed.  We revert the
       declaration to a plain [std::function] and strip [CPPderef] wrappers
       from call sites in the continuation via {!un_deref_var_stmts}.

       If loopification fails (recursion cannot be converted), the original
       shared_ptr pattern is preserved with its body recursively processed. *)
    | Sasgn (id, (Declare Tauto as _ty_opt),
             ( CPPfun_call ({cs_yields = Ropaque; _}, CPPalloc (Alloc_heap, func_ty), {rev = []}) as
               init_expr ))
      :: Sassign_expr (CPPderef (CPPvar id2), CPPlambda
        { cl_params = lparams;
          cl_ret = ret_ty_opt;
          cl_body = lbody;
          cl_capture = cap })
      :: rest
      when Id.equal id id2 ->
      ( match try_loopify_lambda id lparams ret_ty_opt lbody cap with
      | Some lbody' ->
        Sdecl (id, func_ty)
        :: Sasgn (id, Existing, CPPlambda
          { cl_params = lparams;
          cl_tparams = [];
            cl_ret = ret_ty_opt;
            cl_body = lbody';
            cl_capture = Immediate })
        :: process_stmts (un_deref_var_stmts id rest)
      | None ->
        let lbody' = process_stmts lbody in
        Sasgn (id, _ty_opt, init_expr)
        :: Sassign_expr (CPPderef (CPPvar id), CPPlambda
          { cl_params = lparams;
          cl_tparams = [];
            cl_ret = ret_ty_opt;
            cl_body = lbody';
            cl_capture = cap })
        :: process_stmts rest )
    (* Pattern 4: Y-combinator local fixpoint from {!gen_local_fix_by_ref}:
       [Sasgn(id, Declare Tauto, CPPlambda(...))] whose last param is a single
       self-reference [_self_*].  Distinct from Pattern 2 ([Some (Tfun _)]) and
       Pattern 3 (a heap-allocating init). *)
    | Sasgn
        ( id,
          (Declare Tauto as tgt),
          CPPlambda
            { cl_params = lparams;
              cl_ret = ret_ty_opt;
              cl_body = lbody;
              cl_capture = cap } )
      :: rest
      when Option.has_some (ycomb_self_id (to_reversed lparams)) ->
      ( match try_loopify_ycomb (to_reversed lparams) ret_ty_opt lbody with
      | Some (lparams', lbody') ->
        Sasgn
          (id, tgt, CPPlambda
            { cl_params = of_reversed lparams';
            cl_tparams = [];
              cl_ret = ret_ty_opt;
              cl_body = lbody';
              cl_capture = cap })
        :: process_stmts rest
      | None ->
        let lbody' = process_stmts lbody in
        Sasgn (id, tgt, CPPlambda
          { cl_params = lparams;
          cl_tparams = [];
            cl_ret = ret_ty_opt;
            cl_body = lbody';
            cl_capture = cap })
        :: process_stmts rest )
    | stmt :: rest -> process_stmt stmt :: process_stmts rest
  and process_lambda l = {l with cl_body = process_stmts l.cl_body}
  and process_expr expr =
    match expr with
    | CPPlambda l -> CPPlambda (process_lambda l)
    | CPPfun_call (res, f, args) ->
      CPPfun_call (res, process_expr f, map_args process_expr args)
    | _ -> map_expr process_expr process_stmt Fun.id expr
  and process_stmt = function
    | Sif (cond, then_br, else_br) ->
      Sif (process_expr cond, process_stmts then_br, process_stmts else_br)
    | Sblock ss -> Sblock (process_stmts ss)
    | Scustom_case (ty, scrut, tyargs, branches, err) ->
      Scustom_case
        ( ty,
          process_expr scrut,
          tyargs,
          List.map
            (fun (ps, ret_ty, b) -> (ps, ret_ty, process_stmts b))
            branches,
          err )
    | Sswitch (scrut, r, branches, default) ->
      Sswitch
        ( process_expr scrut,
          r,
          List.map (fun (id, body) -> (id, process_stmts body)) branches,
          default )
    | Smatch (scrut, branches, default) ->
      Smatch
        ( { scrut with sc_expr = process_expr scrut.sc_expr },
          List.map
            (fun br ->
              { br with
                smb_extra_conds = List.map process_expr br.smb_extra_conds;
                smb_body = process_stmts br.smb_body })
            branches,
          Option.map process_stmts default )
    | Swhile (cond, body) -> Swhile (process_expr cond, process_stmts body)
    | Sexpr e -> Sexpr (process_expr e)
    | Sasgn (id, ty, e) -> Sasgn (id, ty, process_expr e)
    | Sassign_expr (lhs, e) -> Sassign_expr (process_expr lhs, process_expr e)
    | Sreturn (Some e) -> Sreturn (Some (process_expr e))
    | s -> s
  in
  process_stmts body

(** {2 Cofixpoint detection}

    Cofixpoints (corecursive definitions) returning a standard coinductive type
    are wrapped in a [lazy_] thunk by [cofix_wrap] in [translation.ml].  This
    wrapping defers evaluation so the infinite corecursive structure is built
    on demand rather than eagerly.

    {b Why loopification is unnecessary.}  The [lazy_] wrapper means the
    generated C++ function has this shape:

    {v
      shared_ptr<Stream<T>> smap(F f, shared_ptr<Stream<T>> s) {
        return Stream<T>::lazy_([=]() mutable -> shared_ptr<Stream<T>> {
          return Stream<T>::cons(f(hd(s)), smap(f, tl(s)));
        });
      }
    v}

    The entire body — including any recursive calls like [smap(f, tl(s))] —
    is captured inside a [[\=\]] lambda.  When [smap] is called, it {e never
    executes} the recursive call; it just constructs the closure and passes
    it to [lazy_()], which stores it as a thunk.  The function returns in
    O(1) stack frames.  The recursive call is only executed later, when a
    consumer forces the thunk (e.g. via [.v()]).  At that point the original
    call frame is long gone, so there is no stack accumulation.

    Even cofixpoints with multiple recursive calls (e.g. a coinductive tree
    with [Node n (infinite_tree (n+1)) (infinite_tree (n+2))]) are safe: each
    recursive call itself returns a [lazy_] thunk in O(1), so the total stack
    depth when the outer thunk is forced is still bounded.

    {b Why loopification would be incorrect.}  The TMC (Tail Modulo Cons)
    transform patches cons cells in place via [v_mut()], but coinductive
    types store their variant inside [crane::lazy<variant_t>] and expose
    only the immutable [v()] accessor.  Applying TMC to these bodies
    generates invalid C++ that references the nonexistent [v_mut()] method.

    {b Custom-extracted coinductive types} (e.g. [itree] in reified mode)
    bypass the [lazy_] wrapping because [Table.is_coinductive_type] returns
    [false] for custom inductives.  Their bodies are normal (non-lazy) and
    flow through the standard loopification path.

    The post-pass {!loopify_inner_lambdas} is still applied to the full body
    so that any nested [std::function] fixpoints inside the thunk are
    loopified independently. *)

(** Detect a [lazy_]-wrapped cofixpoint body.

    Matches the AST pattern produced by [cofix_wrap] in [translation.ml]
    (lines ~7620--7650 and ~8878--8883).  The pattern is:

    {v
      Sreturn(Some(
        CPPfun_call(
          CPPscope (type_expr, "lazy_", []),
          [CPPlambda
            { cl_params = [];
              cl_ret = Some ret_ty;
              cl_body = inner_body;
              cl_capture = capture }])))
    v}

    This appears as the {e last} statement in the function body.  Cofixpoints
    with [let ... in] bindings before the return (e.g. [unfold]) have prefix
    statements before the [lazy_] return, so we check only the final statement.

    For cofixpoints whose body branches (e.g. an [Sif] at the top level),
    [cofix_wrap] wraps each return expression individually, so the last
    statement is the branch, not a [lazy_] return.  In that case we return
    [false] and the function falls through unchanged — this is safe because
    each branch still returns a [lazy_] thunk (no stack growth), and the
    loopify pass would see recursive calls inside lambdas and classify the
    function as [No_recursion], producing no transformation.

    @param body  The statement list comprising the function body.
    @return [true] if the last statement matches the [lazy_] factory pattern. *)
let has_lazy_body body =
  let rec last_stmt = function
    | [] -> None
    | [s] -> Some s
    | _ :: rest -> last_stmt rest
  in
  match last_stmt body with
  | Some (Sreturn (Some (CPPfun_call (_, 
      CPPscope (_, lazy_id, []),
      {rev = [CPPlambda {cl_params = {rev = []}; cl_ret = Some _; _}]}))))
    when Id.equal lazy_id id_lazy -> true
  | _ -> false

(** Whether the expression tree contains a [lazy_] factory call.
    Used to detect cofixpoint bodies even when the [lazy_] return is buried
    inside branches rather than at the top level (where {!has_lazy_body}
    catches it). *)
let is_lazy_factory_call = function
  | CPPfun_call (_, CPPscope (_, lazy_id, []), _) ->
    Id.equal lazy_id id_lazy
  | _ -> false

let body_contains_lazy_factory body =
  body_exists is_lazy_factory_call body

(** Apply nontail-recursion loopification, trying strategies in priority order:
    {ol
      {- {b Branch dependency} — bail out if any return expression depends on a
         destructured match binding that is also passed to a recursive call
         (the frame-based rewriter can't handle this yet).}
      {- {b TMC} ({!transform_tmc}) — if the recursion is "tail modulo cons"
         (exactly one recursive call wrapped in a single constructor).}
      {- {b General nontail} ({!transform_nontail}) — frame-based stack for all
         other patterns, including multi-call (e.g. fibonacci, tree traversal).}}

    @param param_inits Optional custom initialisers for shadow / [_self]
                       variables. Forwarded to {!transform_tmc} and
                       {!transform_nontail} so that method receivers can be
                       initialised directly from [this].
    @param fn_name     Optional function name for loop-comment annotations
                       (forwarded to {!transform_nontail}).
    @param check       Call checker for identifying recursive calls
    @param tparams     Template parameter context
    @param adopted     A body calling back into this function, to adopt as a
                       second machine entry; see {!transform_nontail}
    @param params      Function parameters [(id, type)]
    @param ret_ty      Return type
    @param body        Function body statements
    @return what the transform did; see {!nontail_result}. *)
let apply_nontail_loopification ?(param_inits = []) ?fn_name ?adopted check
    tparams params ret_ty body =
  let declined reason =
    {nt_body = body; nt_outcome = Lp_declined reason; nt_used_param_inits = false}
  in
  if has_recursive_branch_dependency check body then
    declined "recursive call in a branch condition or dispatch scrutinee"
  else
  let frame () =
    { nt_body =
        transform_nontail ?fn_name ?adopted check tparams params ret_ty body;
      nt_outcome = Lp_frame;
      nt_used_param_inits = false }
  in
  (* A transform may discover mid-flight that the body's shape has no
     per-parameter correspondence to linearise (see {!Not_linearisable}).  That
     is a limitation, not a bug, so record a decline and keep the original
     body. *)
  try
  (* Tail modulo cons reads constructor cells around calls, which
     {!Normalize} took out into temporaries; it reads the body with them put
     back.  Everything else reads the normalized body. *)
  let restored = Cpp_temporaries.own_stmts body in
  match try_tmc_classify check restored with
  | Some ti ->
    (* TMC only rewrites calls that sit directly under a constructor.  A body
       can mix shapes -- one branch conses onto the recursive result while
       another scrutinises it -- and {!try_tmc_classify} accepts it on the
       strength of the branch it does understand, leaving the other branch as a
       real C++ self-call.  That is exactly the stack growth this pass exists to
       remove, so check the postcondition and fall back to the frame transform,
       which handles the scrutinising shape via a continuation frame. *)
    let tmc = transform_tmc ~param_inits tparams check ti params ret_ty restored in
    if classify check tmc = No_recursion then
      {nt_body = tmc; nt_outcome = Lp_tmc; nt_used_param_inits = true}
    else frame ()
  | None -> frame ()
  with Not_linearisable reason -> declined reason

(** Inline an Equations-style "functional" into its knot-tying wrapper.

    Well-founded recursion defined with [Equations] (or the [Fix]/[Wf]
    combinators) extracts as two sibling definitions: a {e functional}
    [f_functional l rec] that performs the real recursion by calling its
    [rec] parameter, and the tied knot [f l = f_functional l f] that passes
    [f] itself as [rec].  At the C++ level this becomes

    {v
      f(x) { return f_functional(x, [](y){ return f(y); }); }
    v}

    Loopify cannot linearise this on its own: the actual recursion is hidden
    behind an opaque helper and an argument lambda it does not control, so the
    frame transform degenerates into a single [CraneEnter] loop that just re-runs
    the body.  We repair it {e before} loopification by inlining the
    functional's body into [f], rewriting every call to the [rec] parameter
    into a direct self-call to [f].  The result is ordinary self-recursion
    (here, two non-tail calls combined with [++]) that {!transform_nontail}
    turns into a proper explicit-stack loop.

    Detection is deliberately narrow — the wrapper's body must contain a call
    to a sibling field whose argument at some position is exactly an
    eta-expansion [fun y => f(y)] of the wrapper itself — so only the knot
    pattern is rewritten.  The functional field is left in place (now unused);
    it is a template and instantiates only on demand. *)
let try_inline_functional_into names body =
  let self_refs = List.map fst names in
  let is_self_ref r = List.exists (Common.globref_equal r) self_refs in
  (* Whether a call head is one of the functions being defined: by its
     global.  A local of the same name -- a recursor's own parameter [f] -- is
     not the function. *)
  let is_self_call = function
    | CPPglob (r, _, _) -> is_self_ref r
    | _ -> false
  in
  (* Is [e] the eta-expansion [fun y => self(y)] of the function being defined?
     Return the call head so the exact self-call form (with its type args) can
     be reused when rewriting the functional's recursive parameter. *)
  let eta_self_head = function
    | CPPlambda
      { cl_params = {rev = [(_, Some y)]};
        cl_body =
          [ Sreturn
              (Some
                 (CPPfun_call
                    ({cs_yields = Ropaque; _}, head, {rev = [CPPvar y']}) ) ) ];
        _ }
      when Id.equal y y' && is_self_call head ->
      Some head
    | _ -> None
  in
  (* Resolve a call target to a registered functional [(params, body)], skipping
     self. *)
  let lookup_functional callee =
    match callee with
    | CPPglob (r, _, _) when not (is_self_call callee) ->
      Hashtbl.find_opt mutual_fn_table r
    | _ -> None
  in
  (* Find, anywhere in [body], a call to a registered functional with an
     eta-self argument.  Returns (g_ret_ty, g_params, g_body, args, k, self_head). *)
  let find_knot body =
    let result = ref None in
    let consider callee args =
      if !result = None then
        match lookup_functional callee with
        | Some {rf_ret_ty = g_ret_ty; rf_params = g_params; rf_body = g_body} ->
          List.iteri
            (fun k a ->
              if !result = None then
                match eta_self_head a with
                | Some head ->
                  result := Some (g_ret_ty, g_params, g_body, args, k, head)
                | None -> () )
            args
        | None -> ()
    in
    let rec ve e =
      ( match e with
      | CPPfun_call (_, callee, args) -> consider callee (to_reversed args)
      | _ -> () );
      ignore (map_expr (fun e' -> ve e'; e') (fun s -> vs s; s) Fun.id e)
    and vs s = ignore (map_stmt (fun e -> ve e; e) (fun s' -> vs s'; s') Fun.id s) in
    List.iter vs body;
    !result
  in
  let inline_into a_body (g_ret_ty, g_params, g_body, args, k, self_head) =
    if List.length g_params <> List.length args then None
    else
      let rec_param_id = fst (List.nth g_params k) in
      (* The parameter at the eta-argument's position must be the one the
         functional recurses through; if it is never called, the args and
         params are misaligned (or this is not the knot pattern) — bail. *)
      let rec_param_called =
        body_exists
          (function
            | CPPfun_call (_, CPPvar id, _) -> Id.equal id rec_param_id
            | _ -> false)
          g_body
      in
      if not rec_param_called then None
      else
      (* Rewrite calls to the [rec] parameter into direct self-calls. *)
      let rec subst_rec e =
        match e with
        | CPPfun_call (res, CPPvar id, cargs) when Id.equal id rec_param_id ->
          CPPfun_call (res, self_head, map_args subst_rec cargs)
        | _ -> map_expr subst_rec subst_stmt Fun.id e
      and subst_stmt s = map_stmt subst_rec subst_stmt Fun.id s in
      let g_body = List.map subst_stmt g_body in
      (* Bail if the [rec] parameter is used in any non-call position we did
         not rewrite — the simple self-call substitution would be unsound. *)
      let uses_rec_param =
        body_exists (function CPPvar id -> Id.equal id rec_param_id | _ -> false)
          g_body
      in
      if uses_rec_param then None
      else
        (* Freshen every identifier the functional binds — parameters, locals,
           match bindings, and lambda parameters — to avoid capturing (or being
           shadowed by) the wrapper's own variables once spliced in.  Lambda
           parameters matter in particular: a filter predicate [fun x => x < p]
           would otherwise collide with a wrapper parameter also named [x],
           confusing the decltype-based frame-field typing. *)
        let bound = ref [] in
        let add id = bound := id :: !bound in
        let rec cb_expr e =
          ( match e with
          | CPPlambda {cl_params = ps; _} ->
            List.iter (fun (_, ido) -> Option.iter add ido) (to_reversed ps)
          | _ -> () );
          ignore (map_expr (fun e' -> cb_expr e'; e') (fun s -> cb_stmt s; s) Fun.id e)
        and cb_stmt s =
          ( match s with
          | Sdecl (id, _) | Sdecl_init (id, _) | Sasgn (id, Declare _, _) ->
            add id
          | Sbind (ids, _) -> List.iter add ids
          | Smatch (scrut, branches, _) ->
            List.iter
              (fun br ->
                Option.iter add br.smb_var;
                List.iter (fun (id, _, _) -> add id) br.smb_field_bindings )
              branches
          | _ -> () );
          ignore (map_stmt (fun e -> cb_expr e; e) (fun s' -> cb_stmt s'; s') Fun.id s)
        in
        let keep_params =
          List.filteri (fun i _ -> i <> k) g_params
        in
        List.iter (fun (pid, _) -> add pid) keep_params;
        List.iter cb_stmt g_body;
        let rename_map =
          List.map
            (fun id -> (id, Generated_name.prefixed "_inl" id))
            !bound
        in
        let rename_var id =
          match List.assoc_opt id rename_map with Some f -> f | None -> id
        in
        let rec ren_expr = function
          | CPPvar id -> CPPvar (rename_var id)
          | CPPlambda l ->
            CPPlambda
              { (map_lambda ren_stmt Fun.id l) with
                cl_params =
                  of_reversed
                    (List.map
                       (fun (ty, ido) -> (ty, Option.map rename_var ido))
                       (to_reversed l.cl_params) ) }
          | e -> map_expr ren_expr ren_stmt Fun.id e
        and ren_stmt s =
          match s with
          | Sasgn (id, ty, e) -> Sasgn (rename_var id, ty, ren_expr e)
          | Sdecl (id, ty) -> Sdecl (rename_var id, ty)
          | Smatch (scrut, branches, default) ->
            Smatch
              ( { scrut with sc_expr = ren_expr scrut.sc_expr },
                List.map
                  (fun br ->
                    { br with
                      smb_var = Option.map rename_var br.smb_var;
                      smb_field_bindings =
                        List.map
                          (fun (id, ty, u) -> (rename_var id, ty, u))
                          br.smb_field_bindings;
                      smb_extra_conds = List.map ren_expr br.smb_extra_conds;
                      smb_body = List.map ren_stmt br.smb_body } )
                  branches,
                Option.map (List.map ren_stmt) default )
          | _ -> map_stmt ren_expr ren_stmt Fun.id s
        in
        let fresh_params =
          List.map (fun (pid, ty) -> (rename_var pid, ty)) keep_params
        in
        let fresh_body = List.map ren_stmt g_body in
        (* Match exactly the knot call: a call to a registered functional whose
           argument at position [k] is the eta-self lambda. *)
        let spec =
          {
            is_target =
              (function
              | CPPfun_call (_, callee, cargs) ->
                let cargs = to_reversed cargs in
                lookup_functional callee <> None
                && List.length cargs = List.length args
                && (match List.nth_opt cargs k with
                   | Some a -> eta_self_head a <> None
                   | None -> false)
              | _ -> false);
            get_args =
              (function
              | CPPfun_call (_, _, cargs) ->
                List.filteri (fun i _ -> i <> k) (to_reversed cargs)
              | _ -> []);
            params = fresh_params;
            body = fresh_body;
            ret_ty = g_ret_ty;
          }
        in
        Some (generic_inline_stmts spec a_body)
  in
  match find_knot body with
  | Some knot -> (
    match inline_into body knot with Some body' -> body' | None -> body )
  | None -> body

(** Hoist recursive calls out of [if]-conditions into preceding let-bindings.

    Loopify's [has_recursive_branch_dependency] guard leaves a function fully
    recursive when a recursive call appears in a branch condition, because the
    frame rewriter cannot keep a move-only cloned subtree alive across the
    branch.  For value-typed results that danger does not apply, and once the
    call is bound to a temporary the condition merely reads a scalar — exactly
    the shape [transform_nontail] already linearises with a resume frame (as it
    does for a recursive [let r := f m in if ... r ...]).

    So, when the return type is trivially copyable, rewrite each
    [if cond[f(x)] then A else B] into [let r := f(x) in if cond[r] then A
    else B].  Binding once also de-duplicates a call that the condition and a
    branch both use.  Only conditions are rewritten (recursive scrutinees are
    already let-bound during match lowering); lambda bodies are not descended
    into, since their calls are not evaluated as part of the condition. *)
let hoist_rec_conditions (check : call_checker)
    (params : (Id.t * cpp_type) list) (ret_ty : cpp_type)
    (stmts : cpp_stmt list) : cpp_stmt list =
  (* The hazard [has_recursive_branch_dependency] guards against is a raw
     pointer stored in the [CraneEnter] frame that dangles once the smart pointer
     it was derived from is moved from.  So the gate is precisely that no
     parameter is a raw pointer: every other parameter shape — scalars, and
     smart pointers or values, which own their referent — stays alive in the
     frame for as long as the frame does.

     Requiring *trivial copyability* instead, as this gate used to, excluded
     every recursion over an inductive type, since those are passed as smart
     pointers. That is the common case and not the dangerous one. *)
  let rec is_raw_ptr = function
    | Tptr _ -> true
    | Tconst t | Tnamespace (_, t) | Tqualified (t, _) -> is_raw_ptr t
    | _ -> false
  in
  if List.exists (fun (_, ty) -> is_raw_ptr ty) params then stmts
  else
    let counter = ref 0 in
    let fresh () =
      incr counter;
      Id.of_string (Printf.sprintf "_rc%d" !counter)
    in
    let bindings = ref [] in
    (* Bind every recursive-call subexpression of [e] to a fresh temporary and
       replace it with a variable reference.  Used for expressions that are
       always evaluated (branch conditions). *)
    let rec hoist_calls e =
      match check e with
      | Some _ ->
        let f = fresh () in
        bindings := (f, e) :: !bindings;
        CPPvar f
      | None -> map_expr hoist_calls (fun s -> s) Fun.id e
    in
    (* Within an always-evaluated expression, hoist recursive calls out of any
       ternary *condition* (which is itself always evaluated) but leave the
       branches — and any other non-condition calls — untouched, so we never
       eagerly evaluate a call the original code guarded. *)
    let rec hoist_ternaries e =
      match e with
      | CPPcond (c, t, f) ->
        CPPcond (hoist_calls c, hoist_ternaries t, hoist_ternaries f)
      | _ -> map_expr hoist_ternaries (fun s -> s) Fun.id e
    in
    let hoist_cond cond =
      bindings := [];
      let cond' = hoist_calls cond in
      (List.rev !bindings, cond')
    in
    (* A scrutinee or condition that {e is} the recursive call loses, on being
       bound to a temporary of the function's return type, whatever cast the
       call carried in expression position.  When that type is the erased
       [std::any], put the cast back: the surrounding construct needs the
       concrete type [want] it dispatches on. *)
    let hoist_cond_as want cond =
      let binds, cond' = hoist_cond cond in
      (* The temporary is declared with the return type, so a [Topaque] in it
         has been written down as [std::any] and the value really is boxed. *)
      match (Ml_type_util.materialise_opaque ret_ty, cond') with
      | Tany, CPPvar _ when want <> Tany ->
        (binds, Cpp_erasure.unbox want cond')
      | _ -> (binds, cond')
    in
    let hoist_expr e =
      bindings := [];
      let e' = hoist_ternaries e in
      (List.rev !bindings, e')
    in
    let binds_to_stmts binds =
      List.map (fun (f, c) -> Sasgn (f, Declare ret_ty, c)) binds
    in
    let rec hs stmts = List.concat_map hstmt stmts
    and hstmt s =
      match s with
      | Sif (cond, t, e) ->
        let binds, cond' = hoist_cond_as ty_bool cond in
        binds_to_stmts binds @ [Sif (cond', hs t, hs e)]
      | Sreturn (Some e) ->
        let binds, e' = hoist_expr e in
        binds_to_stmts binds @ [Sreturn (Some e')]
      | Sasgn (id, ty, e) ->
        let binds, e' = hoist_expr e in
        binds_to_stmts binds @ [Sasgn (id, ty, e')]
      | Sblock ss -> [Sblock (hs ss)]
      | Swhile (c, ss) -> [Swhile (c, hs ss)]
      | Sswitch (e, r, branches, def) ->
        let binds, e' = hoist_cond e in
        binds_to_stmts binds
        @ [ Sswitch
              ( e', r,
                List.map (fun (p, b) -> (p, hs b)) branches,
                Option.map hs def ) ]
      | Scustom_case (ty, scrut, tyargs, branches, err) ->
        let binds, scrut' = hoist_cond_as ty scrut in
        binds_to_stmts binds
        @ [ Scustom_case
              ( ty, scrut', tyargs,
                List.map (fun (ps, rty, b) -> (ps, rty, hs b)) branches,
                err ) ]
      | Smatch (scrut, branches, default) ->
        (* Hoist a recursive call out of the scrutinee (e.g. [let (a,b) := f m
           in ...] destructuring a recursive result). *)
        let binds, scrut_expr' = hoist_cond scrut.sc_expr in
        binds_to_stmts binds
        @ [ Smatch
              ( { scrut with sc_expr = scrut_expr' },
                List.map (fun br -> {br with smb_body = hs br.smb_body})
                  branches,
                Option.map hs default ) ]
      | _ -> [s]
    in
    hs stmts

(** The name to show for a [Dfun] in the loopification report: the label of
    the outermost reference of its qualified name. *)
let fundef_display_name path =
  let label =
    match fst path.dp_outer with
    | GlobRef.ConstRef c -> Label.to_id (Constant.label c)
    | GlobRef.IndRef (ind, _) -> Label.to_id (MutInd.label ind)
    | GlobRef.ConstructRef ((ind, _), _) -> Label.to_id (MutInd.label ind)
    | GlobRef.VarRef v -> v
  in
  Id.to_string label

(** Transform a top-level function definition by loopifying its body.

    This is the main entry point for loopifying a [Dfun]. The transformation
    proceeds in four steps:

    + Register the function in {!mutual_fn_table} so that other functions can
      detect mutual recursion with it.
    + Try to inline mutual recursion partners via {!try_inline_mutual_into},
      converting mutual recursion into self-recursion.
    + Classify the recursion pattern with {!classify} and apply the appropriate
      strategy: {!transform_tail} for tail recursion, or {!transform_nontail}
      for the general case (including multi-call patterns).
    + Post-pass with {!loopify_inner_lambdas} to loopify any self-recursive
      [std::function] lambdas nested within the body.

    For cofixpoints returning a coinductive type, the body is wrapped in a
    [lazy_] thunk by [cofix_wrap].  The recursive calls are captured inside
    the closure and never executed at call time, so the function returns in
    O(1) stack frames and loopification is unnecessary.  We detect the
    [lazy_] pattern via {!has_lazy_body} and skip the main loopification
    pass.  See the {!has_lazy_body} section header for the full rationale.

                     passes and [decltype] generation)
    @param tparams Template parameters of the enclosing declaration
    @param f       The function node; everything but its body is passed
                   through to the result unchanged
    @param params  Parameter list [(Id.t * cpp_type)]
    @param body    Original function body (statement list)
    @return A [Dfun] declaration with the loopified body *)
let transform_fundef_exn ~tparams (f : dfun) params body =
  let names = dfun_path_list f.df_path in
  let ret_ty = f.df_ret in
  (* Register this function for mutual recursion detection *)
  register_fundef names ret_ty params body;
  (* Try to inline mutual recursion partners *)
  let body = try_inline_mutual_into names body in
  (* Inline an Equations-style functional applied to itself so its hidden
     recursion becomes ordinary self-recursion that loopifies. *)
  let body = try_inline_functional_into names body in
  let check = fn_checker names in
  (* Hoist recursive calls out of if-conditions/scrutinees so a value-typed
     condition-dependent recursion can loopify instead of bailing. *)
  let body = hoist_rec_conditions check params ret_ty body in
  let body = expose_tail_calls check body in
  (* Cofixpoint guard: if this function body ends with a [lazy_] return,
     it is a cofixpoint returning a standard coinductive type.  The entire
     body (including recursive calls) is captured inside a [=] lambda and
     never executed at call time — the function returns a thunk in O(1)
     stack frames.  Loopification is unnecessary and TMC would generate
     invalid [v_mut()] calls (see the {!has_lazy_body} section header for
     the full rationale).  We still run [loopify_inner_lambdas] to handle
     any nested [std::function] fixpoints inside the lazy thunk. *)
  let body =
    let name = fundef_display_name f.df_path in
    if has_lazy_body body || body_contains_lazy_factory body then begin
      if classify check body <> No_recursion then
        record_outcome name (Lp_deferred "cofixpoint body is lazy_-wrapped");
      loopify_inner_lambdas ~tparams ~outer_env:params body
    end else
      (* Normal (non-lazy) function — existing path *)
      let kind = classify check body in
      (* Recursion that lives inside a lambda -- a local fixpoint, or an
         inlined mutual partner -- is visible to {!classify} but out of reach
         of the transforms, which never rewrite through a lambda: the machine
         they emit for it pushes nothing and its loop runs once.  Note the
         body now, while it still has the shape the search recognises, so the
         decline names it instead of reporting the generic "a self-call
         survived". *)
      let adopted =
        match kind with
        | Nontail_recursion -> find_adopted check body
        | _ -> None
      in
      let survived = Option.map decline_reason adopted in
      let body, strategy =
        match kind with
        | No_recursion -> (body, None)
        | Tail_recursion ->
          (transform_tail tparams check params ret_ty body, Some Lp_tail)
        | Nontail_recursion ->
          let r =
            apply_nontail_loopification ~fn_name:name ?adopted check tparams
              params ret_ty body
          in
          (r.nt_body, Some r.nt_outcome)
      in
      (* A self-call can sit inside an inner lambda, where the transforms above
         deliberately leave it alone; [loopify_inner_lambdas] is what removes
         it.  Judge the postcondition only once that has run, or every such
         function is reported as declined even though the emitted code holds no
         self-call. *)
      let body = loopify_inner_lambdas ~tparams ~outer_env:params body in
      (match strategy with
       | None -> body
       | Some s -> report_outcome ?survived ~name ~check ~strategy:s body)
  in
  Dfun {f with df_shape = Ddef (params, body)}

(** [naming name f] is [f ()], with [name ()] -- the function being
    transformed -- written into any failure other than a decline.  The name is
    built only then, and spelled by {!Table.kername_of_global}, which cannot
    fail: a lifted helper is not in the nametab.  An internal error in the
    pass otherwise surfaces as a bare [Failure "nth"], which says nothing of
    where in a large development to look. *)
let naming name f =
  try f () with
  | Not_linearisable _ as e -> raise e
  | e when CErrors.noncritical e ->
    let e, info = Exninfo.capture e in
    CErrors.anomaly ~info
      Pp.(str "loopify, transforming " ++ str (name ()) ++ str ": " ++ CErrors.print e)

(** {!transform_fundef_exn}, but a {!Not_linearisable} raised anywhere inside a
    transform is turned into a decline for this one function: the original body
    is emitted unchanged and the outcome is recorded, so a shape the pass cannot
    linearise never aborts the surrounding extraction. *)
let transform_fundef ~tparams (f : dfun) params body =
  let qualified () =
    String.concat "::"
      (List.map
         (fun (r, _) -> Table.kername_of_global r)
         (f.df_path.dp_outer :: f.df_path.dp_inner))
  in
  try naming qualified (fun () -> transform_fundef_exn ~tparams f params body)
  with Not_linearisable reason ->
    record_outcome (fundef_display_name f.df_path) (Lp_declined reason);
    Dfun {f with df_shape = Ddef (params, body)}

(** Transform a struct method by loopifying its body.

    Methods differ from free functions because recursive calls use
    [this->method(args)] rather than [f(args)]. To loopify, we introduce a
    synthetic [_self] parameter that replaces [this] in the body, allowing the
    loop to track which object is being processed across iterations.

    The transformation:
    + Creates a {!method_checker} for the method name.
    + Classifies the recursion pattern.
    + Replaces [CPPthis] with [CPPvar _self] throughout the body.
    + Adds [_self] (with the struct pointer type) to the parameter list.
    + Applies the appropriate loopification strategy.
    + For tail recursion: initializes the shadow variable directly from [this]
      (no separate [_self = this] line needed).
    + For nontail recursion: prepends [_self = this] initialization before the
      loop, since the [CraneEnter] frame references [_self] by name.

    @param tparams        Type parameters
    @param self_ty        C++ type for the struct pointer (e.g.,
                          [Tconst (Tptr (Tglob (...)))])
    @param mf             The method record to transform
    @return An [Fmethod] field with the loopified body *)
let transform_method ~tparams ~self_ty mf =
  (* [tparams] arrives holding only the enclosing struct's parameters.  A
     method's body is written under its own template header too, and a
     parameter declared there is the one most likely to constrain how the body
     may be rewritten -- a callable argument is a method parameter, never a
     struct one. *)
  let tparams = tparams @ mf.mf_tparams in
  let n_params = List.length mf.mf_params in
  (* A static method has no receiver to strip from a call: its calls never
     carry more arguments than it has parameters, so position [0] is never
     read. *)
  let this_pos =
    match mf.mf_receiver with Instance r -> r.this_pos | Static -> 0
  in
  (* Cofixpoint guard: same reasoning as {!transform_fundef} — if the
     method body is [lazy_]-wrapped, the entire body is deferred inside a
     closure and the method returns in O(1) stack frames.  Loopification
     is unnecessary and TMC would be invalid.  See {!has_lazy_body}. *)
  let name = Id.to_string mf.mf_name in
  (* Hoist recursive calls out of conditions and dispatch scrutinees, exactly
     as {!transform_fundef} does. Methods went without this, so a method whose
     recursion fed a branch condition bailed out where the equivalent free
     function loopified. Hoisting runs on the pre-[_self] parameter list: the
     synthetic [_self] raw pointer is added later and would otherwise trip
     the hoister's own raw-pointer gate. *)
  let mf =
    let n_params = List.length mf.mf_params in
    let check =
      method_checker ~n_params ~has_self_param:false ~this_pos
        ?self_ref:mf.mf_globref mf.mf_name
    in
    { mf with
      mf_body =
        hoist_rec_conditions check mf.mf_params mf.mf_ret_type mf.mf_body }
  in
  if has_lazy_body mf.mf_body then begin
    let basic_check =
      method_checker ~n_params ~has_self_param:false ~this_pos
        ?self_ref:mf.mf_globref mf.mf_name
    in
    if classify basic_check mf.mf_body <> No_recursion then
      record_outcome name (Lp_deferred "cofixpoint body is lazy_-wrapped");
    Fmethod mf
  end else
    let basic_check =
      method_checker ~n_params ~has_self_param:false ~this_pos
        ?self_ref:mf.mf_globref mf.mf_name
    in
    ( match classify basic_check mf.mf_body with
    | No_recursion ->
      Fmethod mf
    | (Tail_recursion | Nontail_recursion) as kind ->
      let self_id = id_self in
      let body_with_self = List.map (this_to_self_stmt self_id) mf.mf_body in
      let self_check =
        method_checker ~n_params ~has_self_param:true ~this_pos
          ?self_ref:mf.mf_globref mf.mf_name
      in
      (* Check whether any recursive call has a value-type receiver — a
         temporary such as [Trie::leaf()], whose address would dangle once
         stored in the CraneEnter frame.  Receivers that name existing storage
         ([CPPvar], [CPPthis]) or dereference a smart pointer ([CPPderef]) are
         fine, since the frame holds a pointer into memory that outlives it.

         This must inspect [cs_recv], the receiver as written.  Inspecting
         [cs_args] instead — as this guard used to — is vacuous: the head of
         [cs_args] is whatever [recv_to_self] produced, always a [CPPunop
         ("&", _)] or a [crane_raw] call and so never one of the three safe
         shapes.  The guard therefore fired for *every* method whose recursion
         went through a [CPPaccess_call], declining 120 functions across the
         test corpus that have no value receiver at all. *)
      let calls = collect_stmts self_check ~in_visitor:false body_with_self in
      (* A receiver that names existing storage is only safe when that storage
         itself outlives the loop; a binder of a match on a temporary does
         not. *)
      let unstable =
        unstable_locals
          ~stable:
            (List.fold_left
               (fun s (id, _) -> Id.Set.add id s)
               (Id.Set.singleton self_id) mf.mf_params)
          body_with_self
      in
      let reads_unstable e =
        expr_exists
          (function CPPvar v -> Id.Set.mem v unstable | _ -> false)
          e
      in
      let has_value_receiver =
        List.exists (fun cs ->
          match Option.map receiver_storage cs.cs_recv with
          | None -> false
          | Some r -> if receiver_is_value r then true else reads_unstable r)
          calls
      in
      (* A tail call whose receiver is a value temporary ([t::n(...)]) can
         still be linearised: park the temporary in a local that outlives the
         loop and recurse on that local instead, so the pointer stored for
         [_self] stays valid across the back-edge.  Only safe when the call's
         other arguments do not read the receiver, since the parking
         assignment happens first. *)
      let self_store_ty =
        let rec pointee = function
          | Tref (_, t) | Tconst t -> pointee t
          | Tptr t | Tshared_ptr t -> Some (strip_ref_and_const_type t)
          | _ -> None
        in
        pointee self_ty
      in
      let id_self_store = Id.of_string "_self_store" in
      let park_value_receivers body =
        let mentions_self e =
          expr_exists
            (function CPPvar v -> Id.equal v self_id | CPPthis -> true | _ -> false)
            e
        in
        let changed = ref false in
        let is_value_recv e = receiver_is_value (receiver_storage e) in
        let replace_at pos x l = List.mapi (fun i y -> if i = pos then x else y) l in
        (* [park e] returns the rewritten self-call, with its value receiver
           replaced by a reference to the parking slot, or [None]. *)
        let park e =
          match e with
          | CPPaccess_call (Aarrow, recv, id, args)
            when Id.equal id mf.mf_name
                 && is_value_recv recv
                 && not (List.exists mentions_self args) ->
            Some (recv, CPPaccess_call (Aarrow, CPPvar id_self_store, id, args))
          | CPPfun_call (_, CPPglob (r, targs, x), args)
            when calls_self_glob ~self_ref:mf.mf_globref mf.mf_name r
                 && List.length (to_reversed args) > n_params ->
            let args_normal = call_args args in
            let recv = List.nth args_normal this_pos in
            if
              is_value_recv recv
              && not
                   (List.exists mentions_self
                      (list_remove_at this_pos args_normal) )
            then
              let args' =
                List.rev (replace_at this_pos (CPPvar id_self_store) args_normal)
              in
              Some (recv, CPPfun_call (call_opaque, CPPglob (r, targs, x), of_reversed (args')))
            else None
          | _ -> None
        in
        let rec go_stmt s =
          match s with
          | Sreturn (Some e) when park e <> None ->
            let (recv, call) = Option.get (park e) in
            changed := true;
            Sblock [Sasgn (id_self_store, Existing, recv); Sreturn (Some call)]
          | _ -> map_stmt (fun e -> e) go_stmt Fun.id s
        in
        let body' = List.map go_stmt body in
        if !changed then Some body' else None
      in
      let parked =
        match (kind, self_store_ty) with
        | (Tail_recursion, Some _) -> park_value_receivers body_with_self
        | _ -> None
      in
      let body_with_self, has_value_receiver, self_store_ty =
        match parked with
        | None -> (body_with_self, has_value_receiver, None)
        | Some b ->
          let calls = collect_stmts self_check ~in_visitor:false b in
          let still =
            List.exists
              (fun cs ->
                match cs.cs_recv with
                | None -> false
                | Some r -> receiver_is_value (receiver_storage r) )
              calls
          in
          if still then (body_with_self, has_value_receiver, None)
          else (b, false, self_store_ty)
      in
      if has_value_receiver then begin
        record_outcome name
          (Lp_declined
             "recursive call passes a value-type receiver, whose address \
              cannot be stored in a frame");
        Fmethod mf
      end else
      let self_param = (self_id, self_ty) in
      let augmented_params = self_param :: mf.mf_params in
      let body', needs_init_self =
        match kind with
        | Tail_recursion ->
          ( report_outcome ~name ~check:self_check ~strategy:Lp_tail
              (transform_tail
                 ~param_inits:[(self_id, CPPthis)]
                 tparams
                 self_check
                 augmented_params
                 mf.mf_ret_type
                 body_with_self),
            false )
        | Nontail_recursion ->
          let fn_name = Some name in
          let r =
            apply_nontail_loopification
              ~param_inits:[(self_id, CPPthis)]
              ?fn_name
              self_check tparams
              augmented_params mf.mf_ret_type body_with_self
          in
          let body' =
            report_outcome ~name ~check:self_check ~strategy:r.nt_outcome
              r.nt_body
          in
          (body', not r.nt_used_param_inits)
        | No_recursion -> CErrors.anomaly (Pp.str "loopify: No_recursion cannot appear here")
      in
      (* Declare the parking slot outside the loop so the pointer taken to it
         on the back-edge stays valid for the next iteration. *)
      let body' =
        match self_store_ty with
        | Some ty -> Sdecl (id_self_store, ty) :: body'
        | None -> body'
      in
      if needs_init_self then
        let init_self = Sasgn (self_id, Declare self_ty, CPPthis) in
        Fmethod {mf with mf_body = init_self :: body'}
      else
        Fmethod {mf with mf_body = body'} )

(** Transform a single struct field, loopifying it if it is a method.

    Non-method fields (e.g., [Ffield], [Ftype]) are returned unchanged. For
    [Fmethod] fields, delegates to {!transform_method}.

    @param tparams        Type parameters
    @param self_ty        C++ type for the struct pointer (e.g., [Tconst (Tptr (Tglob (...)))])
    @param (fld, vis, tag) The field, its visibility, and optional tag
    @return The (possibly transformed) field triple *)
let rec transform_field ~tparams ~self_ty (fld, vis, tag) =
  (* Same contract as {!transform_fundef}: a shape the pass cannot linearise
     declines this one field instead of aborting the extraction. *)
  let name = match fld with Fmethod mf -> Id.to_string mf.mf_name | _ -> "a field" in
  try naming (fun () -> name) (fun () -> transform_field_exn ~tparams ~self_ty (fld, vis, tag))
  with Not_linearisable reason ->
    ( match fld with
    | Fmethod _ -> record_outcome name (Lp_declined reason)
    | _ -> () );
    (fld, vis, tag)

and transform_field_exn ~tparams ~self_ty (fld, vis, tag) =
  match fld with
  | Fmethod mf ->
    (transform_method ~tparams ~self_ty mf, vis, tag)
  | Fnested_struct (id, fields) ->
    let fields' =
      List.map (transform_field ~tparams ~self_ty) fields
    in
    (Fnested_struct (id, fields'), vis, tag)
  | _ -> (fld, vis, tag)

(** {2 Mutual recursion inlining}

    When two functions A and B call each other (mutual recursion), inline B's
    body at each call site in A. After inlining, A becomes self-recursive and
    can be loopified normally. B remains unchanged — it calls the (now
    loopified) A. *)

(** Try to inline mutual recursion among the method fields of a struct.
    Returns the modified field list.

    Identifies mutually recursive pairs (A calls B and B calls A), then inlines
    B's body into A's call sites using {!generic_inline_stmts}.  After inlining,
    A becomes self-recursive and can be loopified normally. *)
let try_inline_mutual_fields fields =
  let fundefs =
    List.filter_map
      (fun (f, _, _) ->
        match f with
        | Fmethod mf ->
          Some (mf.mf_name, mf.mf_ret_type, mf.mf_params, mf.mf_body)
        | _ -> None )
      fields
  in
  (* Look for mutual pairs *)
  let find_mutual_pair () =
    let n = List.length fundefs in
    let found = ref None in
    for i = 0 to n - 1 do
      for j = i + 1 to n - 1 do
        if !found = None then
          let name_a, _, _, body_a = List.nth fundefs i in
          let name_b, _, _, body_b = List.nth fundefs j in
          let a_calls_b = body_calls_id name_b body_a in
          let b_calls_a = body_calls_id name_a body_b in
          if a_calls_b && b_calls_a then
            found := Some (i, j)
      done
    done;
    !found
  in
  match find_mutual_pair () with
  | None -> fields
  | Some (i, j) ->
    let name_a, _ret_ty_a, _params_a, _body_a = List.nth fundefs i in
    let name_b, ret_ty_b, params_b, body_b = List.nth fundefs j in
    (* Build an inline_spec that identifies calls to B by name *)
    let spec = {
      is_target =
        (function
          | CPPfun_call (_, CPPvar id, _) -> Id.equal id name_b
          | _ -> false);
      get_args =
        (function CPPfun_call (_, _, args) -> to_reversed args | _ -> []);
      params = params_b;
      body = body_b;
      ret_ty = ret_ty_b;
    } in
    List.map
      (fun (f, vis, tag) ->
        match f with
        | Fmethod mf when Id.equal mf.mf_name name_a ->
          (Fmethod { mf with mf_body = generic_inline_stmts spec mf.mf_body }, vis, tag)
        | _ -> (f, vis, tag) )
      fields


(** Top-level entry point: transform a declaration and all its nested
    declarations (templates, structs, namespaces). Dispatches to
    {!transform_fundef}, {!transform_method}, or recurses for composite
    declarations. *)
let rec transform_decl ?(tparams = []) = function
  | Dtemplate (tparams, constraint_opt, inner) ->
    Dtemplate
      (tparams, constraint_opt, transform_decl ~tparams inner)
  | Dfun ({df_shape = Ddef (params, body); _} as f) ->
    transform_fundef ~tparams f params body
  | Dstruct ds ->
    (* Name the struct's own template arguments: inside a nested inductive the
       receiver type is spelled through its module ([typename List::template
       list<A>]), and the bare template name there is not a type. *)
    let self_args =
      List.map
        (fun (_, id) -> named_tvar id)
        (if ds.ds_tparams = [] then tparams else ds.ds_tparams)
    in
    let self_ty = Tconst (Tptr (Tglob (ds.ds_ref, self_args, []))) in
    (* Try inlining mutual recursion among struct fields before transforms *)
    let fields = try_inline_mutual_fields ds.ds_fields in
    (* Collect smart-pointer field indices from variant structs for TMC *)
    let rec collect_uptr_fields (fld, _vis, _tag) =
      match fld with
      | Fnested_struct (id, sub_fields) ->
        let ctor_name = Id.to_string id in
        let var_fields =
          List.filter_map
            (fun (f, _, _) -> match f with Fvar (_, ty) -> Some ty | _ -> None)
            sub_fields
        in
        let ptr_fields =
          List.mapi
            (fun i ty ->
              match ty with
              | Tshared_ptr (Tglob (r, _, _)) when Common.globref_equal r ds.ds_ref ->
                Some (Recursive i)
              | Tshared_ptr _ -> Some (Boxed i)
              | _ -> None)
            var_fields
          |> List.filter_map Fun.id
        in
        if ptr_fields <> [] then
          Hashtbl.replace ctor_ptr_fields
            (Common.ctor_owner_key ds.ds_ref, ctor_name) ptr_fields;
        List.iter collect_uptr_fields sub_fields
      | _ -> ()
    in
    List.iter collect_uptr_fields fields;
    Dstruct
      {
        ds with
        ds_fields =
          List.map
            (transform_field ~tparams ~self_ty)
            fields;
      }
  | Dfields ds ->
    (* A promoted inductive's members are transformed exactly as they would be
       inside their own struct; only the wrapper differs. *)
    ( match transform_decl ~tparams (Dstruct ds) with
    | Dstruct ds' -> Dfields ds'
    | d -> d )
  | Dnspace (r, decls) ->
    (* Pre-register all functions for mutual recursion detection before
       transforming *)
    List.iter register_decl decls;
    Dnspace (r, List.map (transform_decl ~tparams) decls)
  | d -> d
