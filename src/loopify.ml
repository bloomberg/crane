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

    Uses explicit stack with [_Enter] and [_Call] frames. The [_Enter] frame
    initiates computation; [_Call] frames save continuation context.

    {3 Multi-Recursion (2+ Calls per Branch)}
    [fib n = if n < 2 then 1 else fib(n-1) + fib(n-2)]

    Uses chained [_Call] frames or [_Enter/_After/_Combine] pattern to handle
    multiple recursive calls in the same expression.

    {2 Architecture}

    The pass operates in several stages:

    1. {b Classification}: Analyze function body to determine recursion kind
       (tail, non-tail, multi-call) via {!classify}

    2. {b Transformation}: Apply appropriate strategy:
       - {!transform_tail} for tail recursion → while loop with shadow vars
       - {!transform_nontail} for non-tail → frame-based stack
       - {!transform_multi} for multi-call → specialized frame patterns

    3. {b Decomposition}: Break down complex expressions with recursive calls:
       - {!decompose_single_call} for 1 recursive call
       - {!decompose_double_call} for 2 recursive calls
       - {!decompose_all_calls} for N recursive calls

    4. {b Frame Generation}: Create typed frame structs ([_Enter], [_CallN])
       and dispatch loop with [std::visit(Overloaded\{...\}, frame)]

    {2 Reuse Optimization Bypass}

    The escape analysis pass ([translation.ml]) generates dual-path code for
    pattern matches: a fast path that mutates cons cells in-place when
    [use_count() == 1], and a normal path that allocates fresh nodes.  The fast
    path uses [Sassign_field] statements that the loopify rewriters cannot
    decompose.  When this happens, the loopified [Sif] handler detects the
    residual recursive calls in the reuse branch (via {!count_calls_stmts}),
    confirms the condition is a reuse-optimization guard (via
    {!is_reuse_optimization_cond}), and drops the fast path entirely, keeping
    only the properly loopified normal path.

    {2 Decltype Rewriting}

    Frame struct fields with unknown types fall back to [decltype(expr)].  If
    [expr] references lambda-scoped variables that are not in scope at the
    struct definition level, the C++ will fail to compile.  The function
    {!rewrite_field_access_for_decltype} rewrites both plain variable
    references and field accesses to [std::declval<T&>()] forms, making the
    [decltype] expression valid at struct scope.

    {2 Limitations}

    {b Inner Lambdas Calling Outer Functions:} When an inner lambda (from Coq's
    [let fix]) calls the outer function being loopified, the call remains as
    explicit C++ recursion. This is because inner and outer functions have
    incompatible frame types (different [std::variant] types) and cannot share
    a stack. To avoid this, restructure the Coq code so that inner fixpoints
    become top-level self-recursive helpers (possibly with fuel parameters).

    {2 Entry Points}

    - {!transform_fundef}: Transform a top-level function definition
    - {!transform_method}: Transform a struct method
    - {!loopify_decl}: Main dispatch for all declaration types

    @since Crane 1.0 *)

open Names
open Minicpp

(** Check whether a C++ return type is a value-type inductive (non-coinductive,
    non-enum bare [Tglob]).  When true, TMC must wrap [_head]/_write in
    [shared_ptr] because the constructor's recursive field is [shared_ptr].
    Handles [Tnamespace] wrapping for out-of-line (.cpp) method definitions. *)
let rec is_value_type_ret = function
  | Tglob (r, _, _) -> not (Table.is_coinductive r) && not (Table.is_custom r)
  | Tnamespace (_, t) -> is_value_type_ret t
  | _ -> false

(** {2 Mutual recursion table}

    Functions register their bodies here so mutual pairs can be detected and
    inlined during the loopify pass. Keyed by GlobRef. *)

(** Table mapping GlobRef → (params, body) for function definitions. *)
let mutual_fn_table :
    (GlobRef.t, (Id.t * cpp_type) list * cpp_stmt list) Hashtbl.t =
  Hashtbl.create 32

(** Register a function definition for mutual recursion detection. Each
    [GlobRef.t] in [refs] maps to the function's parameters and body. *)
let register_fundef
    (refs : (GlobRef.t * cpp_type list) list)
    (params : (Id.t * cpp_type) list)
    (body : cpp_stmt list) =
  List.iter
    (fun (r, _) -> Hashtbl.replace mutual_fn_table r (params, body))
    refs

(** Clear the mutual recursion table. Called between extraction units. *)
let clear_mutual_table () = Hashtbl.clear mutual_fn_table

(** {2 Recursion classification} *)

(** Information about a single recursive call site. *)
type call_site = {
  cs_args : cpp_expr list;  (** Arguments to the recursive call *)
  cs_is_tail : bool;  (** Whether this call appears in tail position *)
}

(** Classification of a function body's recursion pattern. *)
type recursion_kind =
  | No_recursion  (** No recursive calls found *)
  | Tail_recursion  (** All recursive calls are in tail position *)
  | Nontail_recursion  (** At least one non-tail recursive call *)

(** {2 Call checker abstraction}

    A [call_checker] is a function that recognises recursive calls in
    expressions. It returns [Some call_site] when the expression is a direct
    recursive call, and [None] otherwise. Different checkers are used for
    top-level functions ({!fn_checker}) vs methods ({!method_checker}) vs inner
    lambdas ({!lambda_checker}). *)

(** Type alias for recursive call detection functions. Given a [cpp_expr],
    returns [Some call_site] if it is a direct recursive call, [None] otherwise. *)
type call_checker = cpp_expr -> call_site option

(** Check whether a [GlobRef.t] matches any of the given function refs. *)
let ref_matches fn_refs r =
  List.exists
    (fun (fn_r, _) -> Environ.QGlobRef.equal Environ.empty_env r fn_r)
    fn_refs

(** Build a call checker for top-level function definitions. Matches both
    [CPPglob]-based calls (from Rocq extraction) and [CPPvar]-based calls (local
    references by name). *)
let fn_checker (fn_refs : (GlobRef.t * cpp_type list) list) : call_checker =
 fun e ->
   match e with
   | CPPfun_call (CPPglob (r, _, _), args) when ref_matches fn_refs r ->
     Some {cs_args = args; cs_is_tail = false}
   | CPPfun_call (CPPvar id, args) ->
     let matches_name =
       List.exists
         (fun (r, _) ->
           let label =
             match r with
             | GlobRef.ConstRef c -> Label.to_id (Constant.label c)
             | GlobRef.IndRef (ind, _) -> Label.to_id (MutInd.label ind)
             | GlobRef.ConstructRef ((ind, _), _) ->
               Label.to_id (MutInd.label ind)
             | GlobRef.VarRef v -> v
           in
           Id.equal id label )
         fn_refs
     in
     if matches_name then
       Some {cs_args = args; cs_is_tail = false}
     else
       None
   | _ -> None

(** Build a call checker for struct methods. Matches [CPPmethod_call] on
    [method_name] and, when [has_self_param] is true, includes the receiver
    pointer as the first argument. Also matches [CPPglob] calls that resolve to
    the same method name. *)
let method_checker
    ~(n_params : int)
    ~(has_self_param : bool)
    ~(this_pos : int)
    (method_name : Id.t) : call_checker =
 (* Convert a receiver expression to a raw pointer for the _Enter struct.
    Unwrap CPPderef: deref(shared_ptr) uses shared_ptr.get() directly.
    Otherwise apply .get() to the expression itself. *)
 let recv_to_ptr recv =
   match recv with
   | CPPderef inner ->
     CPPfun_call (CPPmember (inner, Id.of_string "get"), [])
   | _ ->
     CPPfun_call (CPPmember (recv, Id.of_string "get"), [])
 in
 let extract_at pos lst =
   let rec aux i acc = function
     | [] -> (None, List.rev acc)
     | x :: rest ->
       if i = pos then (Some x, List.rev_append acc rest)
       else aux (i + 1) (x :: acc) rest
   in
   aux 0 [] lst
 in
 fun e ->
   match e with
   | CPPmethod_call (recv, id, args) when Id.equal id method_name ->
     if has_self_param then
       Some {cs_args = recv_to_ptr recv :: args; cs_is_tail = false}
     else
       Some {cs_args = args; cs_is_tail = false}
   | CPPfun_call (CPPvar id, args) when Id.equal id method_name ->
     let args_normal = List.rev args in
     if has_self_param && List.length args_normal > n_params then
       let self_arg, rest = extract_at this_pos args_normal in
       ( match self_arg with
       | Some recv ->
         Some {cs_args = recv_to_ptr recv :: rest; cs_is_tail = false}
       | None -> Some {cs_args = args_normal; cs_is_tail = false} )
     else if (not has_self_param) && List.length args_normal > n_params then
       Some {cs_args = List.filteri (fun i _ -> i <> this_pos) args_normal;
             cs_is_tail = false}
     else
       Some {cs_args = args_normal; cs_is_tail = false}
   | CPPfun_call (CPPglob (r, _, _), args) ->
     let label =
       match r with
       | GlobRef.ConstRef c -> Label.to_id (Constant.label c)
       | GlobRef.IndRef (ind, _) -> Label.to_id (MutInd.label ind)
       | GlobRef.ConstructRef ((ind, _), _) -> Label.to_id (MutInd.label ind)
       | GlobRef.VarRef v -> v
     in
     if Id.equal label method_name then
       let args_normal = List.rev args in
       if has_self_param then
         let self_arg, rest = extract_at this_pos args_normal in
         ( match self_arg with
         | Some recv ->
           Some {cs_args = recv_to_ptr recv :: rest; cs_is_tail = false}
         | None -> Some {cs_args = args_normal; cs_is_tail = false} )
       else
         let args_stripped =
           if List.length args_normal > n_params then
             List.filteri (fun i _ -> i <> this_pos) args_normal
           else
             args_normal
         in
         Some {cs_args = args_stripped; cs_is_tail = false}
     else
       None
   | _ -> None

(** {2 Call collection} *)

(** Collect all recursive call sites from an expression. Returns a list of
    {!call_site} values, one per recursive call found. Does NOT descend into
    inner lambda bodies for counting (those are handled separately via
    {!collect_stmts}). *)
let rec collect_expr (check : call_checker) expr =
  match check expr with
  | Some cs ->
    (* Also look for nested calls in the arguments (e.g., f(m', f(m, n'))) *)
    let nested =
      match expr with
      | CPPfun_call (_, args) -> List.concat_map (collect_expr check) args
      | CPPmethod_call (_, _, args) -> List.concat_map (collect_expr check) args
      | _ -> []
    in
    cs :: nested
  | None ->
  match expr with
  | CPPfun_call (f, args) ->
    collect_expr check f @ List.concat_map (collect_expr check) args
  | CPPmethod_call (obj, _id, args) ->
    collect_expr check obj @ List.concat_map (collect_expr check) args
  | CPPmove e | CPPderef e | CPPforward (_, e) | CPPnamespace (_, e) ->
    collect_expr check e
  | CPPoverloaded exprs -> List.concat_map (collect_expr check) exprs
  | CPPlambda (_, _, stmts, _) ->
    (* Calls inside lambdas found via collect_expr are NOT tail calls of the
       outer function — they're returns from the lambda, whose result is used in
       a larger expression (e.g., Cons_(x, visit(l, {... => f(args)}))). The
       direct visit-in-return case goes through collect_stmt's special case for
       Sreturn(Some(visit(...))), not through here. *)
    List.map
      (fun cs -> {cs with cs_is_tail = false})
      (collect_stmts check ~in_visitor:false stmts)
  | CPPget (e, _)
   |CPPget' (e, _)
   |CPPmember (e, _)
   |CPParrow (e, _)
   |CPPqualified (e, _) -> collect_expr check e
  | CPPstructmk (_, _, args)
   |CPPstruct (_, _, args)
   |CPPstruct_id (_, _, args)
   |CPPnew (_, args) -> List.concat_map (collect_expr check) args
  | CPPshared_ptr_ctor (_, e) | CPPunique_ptr_ctor (_, e) ->
    collect_expr check e
  | CPPbinop (_, e1, e2) -> collect_expr check e1 @ collect_expr check e2
  | CPPparray (arr, def) ->
    Array.fold_left
      (fun acc e -> acc @ collect_expr check e)
      (collect_expr check def)
      arr
  | CPPvar _
   |CPPglob _
   |CPPvisit
   |CPPmk_shared _
   |CPPmk_unique _
   |CPPthis
   |CPPshared_from_this _
   |CPPconvertible_to _
   |CPPabort _
   |CPPenum_val _
   |CPPraw _
   |CPPbool _
   |CPPint _
   |CPPbrace_init
   |CPPunop _
   |CPPany_cast _
   |CPPstring _
   |CPPuint _
   |CPPfloat _
   |CPPrequires _ -> []

(** Collect recursive call sites from a list of statements.
    Delegates to {!collect_stmt} for each statement. *)
and collect_stmts check ~in_visitor stmts =
  (* Detect void tail-call patterns at the end of a statement list.

     Pattern A — [Sexpr call; Sreturn None]:
     In C++, a void function can end with [f(); return;] which is
     semantically [return f();] — the call is in tail position.
     Generated by cofix_wrap and gen_stmts when current_cpp_return_type
     is Tvoid.

     Pattern B — [Sexpr call; Sreturn (Some val)]:
     Same situation but generated when current_cpp_return_type is a unit
     type (not Tvoid), e.g. for ITree-unit-returning fixpoints whose
     return is threaded through the nat-match continuation [k].  The
     generated code is [f(); return Unit::e_TT;] which is semantically
     equivalent — [f()] is still the last meaningful call before the
     function exits.  Without this pattern the call would be found only
     via collect_expr (cs_is_tail = false), misclassifying the function
     as Nontail_recursion and producing an unnecessary explicit stack. *)
  let rec go = function
    | Sexpr e :: Sreturn None :: rest ->
      collect_stmt check ~in_visitor (Sreturn (Some e)) @ go rest
    | Sexpr e :: Sreturn (Some _) :: rest ->
      collect_stmt check ~in_visitor (Sreturn (Some e)) @ go rest
    | s :: rest ->
      collect_stmt check ~in_visitor s @ go rest
    | [] -> []
  in
  go stmts

(** Collect recursive call sites from a single statement. Handles
    [Sreturn], [Sif], [Scustom_case], [Sswitch], and nested visit lambdas.
    When [~in_visitor:true], return-position calls are treated as tail calls. *)
and collect_stmt check ~in_visitor = function
  | Sreturn (Some e) ->
    ( match check e with
    | Some cs ->
      (* Also look for nested calls in arguments (e.g., f(m', f(m, n'))) *)
      let nested =
        match e with
        | CPPfun_call (_, args) -> List.concat_map (collect_expr check) args
        | CPPmethod_call (_, _, args) ->
          List.concat_map (collect_expr check) args
        | _ -> []
      in
      {cs with cs_is_tail = true} :: nested
    | None ->
    match e with
    | CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas]) ->
      collect_expr check scrut
      @ List.concat_map
          (fun lambda ->
            match lambda with
            | CPPlambda (_, _, body, _) ->
              collect_stmts check ~in_visitor:true body
            | _ -> collect_expr check lambda )
          lambdas
    | _ -> collect_expr check e )
  | Sreturn None -> []
  | Sexpr e -> collect_expr check e
  | Sasgn (_, _, e) | Sderef_asgn (_, e) -> collect_expr check e
  | Sif (cond, then_br, else_br) ->
    collect_expr check cond
    @ collect_stmts check ~in_visitor then_br
    @ collect_stmts check ~in_visitor else_br
  | Swhile (cond, body) ->
    collect_expr check cond @ collect_stmts check ~in_visitor body
  | Sblock stmts -> collect_stmts check ~in_visitor stmts
  | Sswitch (scrut, _, branches, _) ->
    collect_expr check scrut
    @ List.concat_map
        (fun (_, body) -> collect_stmts check ~in_visitor body)
        branches
  | Scustom_case (_, scrut, _, branches, _) ->
    collect_expr check scrut
    @ List.concat_map
        (fun (_, _, body) -> collect_stmts check ~in_visitor body)
        branches
  | Sassign_field (obj, _, e) -> collect_expr check obj @ collect_expr check e
  | Sblock_custom (_, _, _, _, args, _) ->
    List.concat_map (collect_expr check) args
  | Smatch (branches, default) ->
    List.concat_map
      (fun br ->
        collect_expr check br.smb_scrutinee
        @ List.concat_map (collect_expr check) br.smb_extra_conds
        @ ( match br.smb_reuse with
          | Some (cond, _, stmts) ->
            collect_expr check cond
            @ collect_stmts check ~in_visitor:true stmts
          | None -> [] )
        @ collect_stmts check ~in_visitor:true br.smb_body)
      branches
    @ ( match default with
      | Some stmts -> collect_stmts check ~in_visitor stmts
      | None -> [] )
  | Sdecl _ | Sthrow _ | Sassert _ | Sraw _ | Sstruct_def _ | Susing _
  | Sdecl_init _ | Scontinue | Sbreak -> []

(** Count recursive calls in an expression (not descending into lambdas). *)
let rec count_calls_expr (check : call_checker) expr =
  match check expr with
  | Some _ -> 1
  | None ->
  match expr with
  | CPPfun_call (f, args) ->
    count_calls_expr check f
    + List.fold_left (fun acc a -> acc + count_calls_expr check a) 0 args
  | CPPmethod_call (obj, _, args) ->
    count_calls_expr check obj
    + List.fold_left (fun acc a -> acc + count_calls_expr check a) 0 args
  | CPPmove e | CPPderef e | CPPforward (_, e) | CPPnamespace (_, e) ->
    count_calls_expr check e
  | CPPbinop (_, e1, e2) ->
    count_calls_expr check e1 + count_calls_expr check e2
  | CPPget (e, _)
   |CPPget' (e, _)
   |CPPmember (e, _)
   |CPParrow (e, _)
   |CPPqualified (e, _) -> count_calls_expr check e
  | CPPstructmk (_, _, args)
   |CPPstruct (_, _, args)
   |CPPstruct_id (_, _, args)
   |CPPnew (_, args) ->
    List.fold_left (fun acc a -> acc + count_calls_expr check a) 0 args
  | CPPshared_ptr_ctor (_, e) | CPPunique_ptr_ctor (_, e) ->
    count_calls_expr check e
  | CPPoverloaded exprs ->
    List.fold_left (fun acc a -> acc + count_calls_expr check a) 0 exprs
  | _ -> 0

(** Count recursive calls in a statement list. *)
let rec count_calls_stmts (check : call_checker) stmts =
  List.fold_left
    (fun acc stmt ->
      acc
      +
      match stmt with
      | Sreturn (Some e) | Sexpr e | Sasgn (_, _, e) | Sderef_asgn (_, e) ->
        count_calls_expr check e
      | Sif (cond, then_br, else_br) ->
        count_calls_expr check cond
        + count_calls_stmts check then_br
        + count_calls_stmts check else_br
      | Sblock ss -> count_calls_stmts check ss
      | Sswitch (e, _, branches, _) ->
        count_calls_expr check e
        + List.fold_left
            (fun acc (_, body) -> acc + count_calls_stmts check body)
            0
            branches
      | Scustom_case (_, scrut, _, branches, _) ->
        count_calls_expr check scrut
        + List.fold_left
            (fun acc (_, _, body) -> acc + count_calls_stmts check body)
            0
            branches
      | Sassign_field (obj, _, e) ->
        count_calls_expr check obj + count_calls_expr check e
      | Smatch (branches, default) ->
        List.fold_left
          (fun acc br ->
            acc + count_calls_expr check br.smb_scrutinee
            + List.fold_left (fun a c -> a + count_calls_expr check c) 0 br.smb_extra_conds
            + ( match br.smb_reuse with
              | Some (cond, _, stmts) ->
                count_calls_expr check cond + count_calls_stmts check stmts
              | None -> 0 )
            + count_calls_stmts check br.smb_body )
          0 branches
        + (match default with Some ss -> count_calls_stmts check ss | None -> 0)
      | _ -> 0 )
    0
    stmts

(** Detect if a condition expression is a reuse-optimization guard generated by
    the escape analysis / translation pass.  These have the shape
    [scrut.use_count() == 1 && scrut->v().index() == N].  The left conjunct
    always calls [use_count], which is a reliable discriminator. *)
let rec is_reuse_optimization_cond = function
  | CPPbinop ("&&", l, _) -> is_reuse_optimization_cond l
  | CPPbinop ("==", CPPfun_call (CPPmember (_, id), []), _) ->
    String.equal (Id.to_string id) "use_count"
  | _ -> false

(** Apply reuse-optimization bypass to a rewritten [Sif].
    If [cond] is a use-count guard and the then-branch still contains
    un-decomposed recursive calls while the else-branch is clean,
    drops the then-branch entirely and returns only the else-branch. *)
let rewrite_if_with_reuse_bypass check cond rw_then rw_else =
  if is_reuse_optimization_cond cond
     && count_calls_stmts check rw_then > 0
     && count_calls_stmts check rw_else = 0
  then rw_else
  else [Sif (cond, rw_then, rw_else)]

(** Classify a function body's recursion pattern. Collects all recursive call
    sites and checks whether they are all in tail position, some non-tail, or
    none at all. *)
let classify check body =
  let calls = collect_stmts check ~in_visitor:false body in
  match calls with
  | [] -> No_recursion
  | _ ->
    if List.for_all (fun cs -> cs.cs_is_tail) calls then
      Tail_recursion
    else
      Nontail_recursion

(** {2 Invariant parameter detection}

    A parameter is invariant if every recursive call site passes it unchanged
    (i.e., the argument at that position is [CPPvar id] where [id] is the
    parameter name). Invariant parameters need not appear in frame structs or
    shadow variables — they can be referenced directly from function scope. *)

(** Returns a bool list parallel to [params]: [true] = varying, [false] =
    invariant. *)
let find_varying_params check params body =
  let calls = collect_stmts check ~in_visitor:false body in
  if calls = [] then
    List.map (fun _ -> true) params
  else
    List.mapi
      (fun i (id, _ty) ->
        not
          (List.for_all
             (fun cs ->
               match List.nth_opt cs.cs_args i with
               | Some (CPPvar arg_id) -> Id.equal arg_id id
               | _ -> false )
             calls ) )
      params

(** Filter a list keeping only elements at positions where [mask] is [true]. *)
let filter_by_mask mask lst = List.filteri (fun i _ -> List.nth mask i) lst

(** Build a [std::visit(Overloaded\{...\}, scrut)] expression. *)
let make_visit_expr scrut lambdas =
  CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas])

(** Wrap a [std::visit] dispatch into a single-statement list. *)
let make_visit_stmt scrut lambdas =
  [Sexpr (make_visit_expr scrut lambdas)]

(** Rewrite each lambda body in a visitor and set its return type.
    Non-lambda expressions are passed through unchanged.
    @param ret_ty   New return type for each lambda
    @param rewrite  [lparams -> body -> new_body] transformation *)
let map_visit_lambdas ~ret_ty ~rewrite lambdas =
  List.map
    (fun lambda ->
      match lambda with
      | CPPlambda (lparams, _ret_ty, body, _capture) ->
        CPPlambda (lparams, ret_ty, rewrite lparams body, false)
      | e -> e)
    lambdas

(** {2 This→_self substitution for method loopification} *)

(** Replace [CPPthis] with [CPPvar self_id] throughout an expression. *)
let rec this_to_self_expr (self_id : Id.t) (e : cpp_expr) : cpp_expr =
  match e with
  | CPPthis -> CPPvar self_id
  | _ ->
    map_expr (this_to_self_expr self_id) (this_to_self_stmt self_id) Fun.id e

(** Replace [CPPthis] with [CPPvar self_id] throughout a statement. *)
and this_to_self_stmt (self_id : Id.t) (s : cpp_stmt) : cpp_stmt =
  map_stmt (this_to_self_expr self_id) (this_to_self_stmt self_id) Fun.id s

(** {2 Variable substitution} *)

(** Substitute variable names in an expression using a mapping
    [(old_id, new_id)]. *)
let rec subst_expr (subs : (Id.t * Id.t) list) e =
  let e' =
    List.fold_left
      (fun acc (old_id, new_id) ->
        match acc with
        | CPPvar id when Id.equal id old_id -> CPPvar new_id
        | _ -> acc )
      e
      subs
  in
  map_expr (subst_expr subs) (subst_stmt subs) (fun t -> t) e'

(** Substitute variable names in a statement using a mapping
    [(old_id, new_id)]. Statement-level companion of {!subst_expr}. *)
and subst_stmt subs s =
  map_stmt (subst_expr subs) (subst_stmt subs) (fun t -> t) s

(** {2 Tail recursion transformation}

    For std::visit-based bodies, we use a [_continue] flag in the while
    condition. Visit lambdas are void-returning: base cases assign to [_result]
    and set [_continue = false] to exit the loop; recursive cases just update
    shadow params (the flag stays [true]).

    {[
      RetType _result\{\};
      auto _loop_x = x; auto _loop_l = l;
      bool _continue = true;
      while (_continue) \{
        std::visit(Overloaded\{
          [&](Base _args) \{ _result = base_val; _continue = false; \},
          [&](Rec _args) \{
            _loop_x = new_x; _loop_l = new_l;
          \}
        \}, _loop_l->v());
      \}
      return _result;
    ]} *)

(** Create a shadow variable name for tail-recursion loop variables.
    Prefixes [id] with [_loop_], avoiding C++'s reserved double-underscore. *)
let shadow_name (id : Id.t) : Id.t =
  let s = Id.to_string id in
  (* Avoid double underscores (reserved in C++): _loop_ + _self → _loop_self *)
  if String.length s > 0 && s.[0] = '_' then
    Id.of_string ("_loop" ^ s)
  else
    Id.of_string ("_loop_" ^ s)

(** Strip reference and const modifiers from a type, converting it to a value
    type suitable for local variable declarations. [const shared_ptr<T> &]
    becomes [shared_ptr<T>], and [F0 &&] (= [Tref(Tref(Tvar))]) becomes [Tvar].
*)
let rec strip_ref_type = function
  | Tref t -> strip_ref_type t
  | t -> t

(** Strip reference types AND const modifiers from a type. Used for shadow
    variables in tail recursion, which must be mutable to support reassignment
    in the loop body.  However, [const] on a pointer pointee is preserved:
    [const tree *] stays [const tree *] because the pointer variable itself is
    mutable (can be reassigned), while the [const] just prevents modification
    through the pointer — removing it would break [_loop_self = this] when
    [this] is [const T *] in a const method. *)
let rec strip_ref_and_const_type = function
  | Tref t -> strip_ref_and_const_type t
  | Tmod (TMconst, Tptr _) as t -> t
  | Tmod (TMconst, t) -> strip_ref_and_const_type t
  | t -> t

(** Return [true] when a parameter type can be safely moved into a shadow
    variable.  References cannot be moved from; const values would trigger
    a pessimizing-move warning since the move constructor receives [const T&&]
    and falls back to copy anyway. *)
let is_moveable_param_type = function
  | Tref _ -> false
  | Tmod (TMconst, _) -> false
  | _ -> true

(** Assign [expr] to the [_result] accumulator variable.
    Generates the statement list [[\[_result = expr;\]]]. *)
let assign_result expr =
  [Sexpr (CPPbinop ("=", CPPvar (Id.of_string "_result"), expr))]

(** Assign [expr] to [_result] and set [_continue = false] to exit
    the tail-recursion while loop.  Used only in tail-recursion rewriting. *)
let assign_result_and_stop expr =
  [ Sexpr (CPPbinop ("=", CPPvar (Id.of_string "_result"), expr));
    Sbreak ]

(** Generate temp-based parameter updates to avoid read-after-write hazards. For
    a recursive call like [f b (a mod b)], we must evaluate all argument
    expressions (which reference _loop_ variables) before overwriting any of
    them. We emit: auto _next_a = expr_for_a; auto _next_b = expr_for_b; _loop_a
    = std::move(_next_a); _loop_b = std::move(_next_b);

    Self-assignments (_loop_x = _loop_x) are skipped entirely. When there is
    only one non-trivial assignment the temps are unnecessary but harmless. *)
let make_shadow_updates shadow_params args =
  let pairs = List.combine shadow_params args in
  (* Identify which params actually change *)
  let non_trivial =
    List.filter
      (fun ((_shadow_id, _ty), arg) ->
        match arg with
        | CPPvar id when Id.equal id _shadow_id -> false
        | _ -> true )
      pairs
  in
  if List.length non_trivial <= 1 then
    (* 0 or 1 assignment — no hazard possible, assign directly *)
    List.filter_map
      (fun ((shadow_id, _ty), arg) ->
        match arg with
        | CPPvar id when Id.equal id shadow_id -> None
        | _ -> Some (Sasgn (shadow_id, None, arg)) )
      pairs
  else (* 2+ assignments — use temporaries *)
    let temp_name (id : Id.t) : Id.t =
      let s = Id.to_string id in
      let base =
        if String.length s > 6 && String.sub s 0 6 = "_loop_" then
          String.sub s 6 (String.length s - 6)
        else if String.length s > 5 && String.sub s 0 5 = "_loop" then
          String.sub s 5 (String.length s - 5)
        else
          s
      in
      (* Avoid double underscores (reserved in C++) *)
      if String.length base > 0 && base.[0] = '_' then
        Id.of_string ("_next" ^ base)
      else
        Id.of_string ("_next_" ^ base)
    in
    let temp_decls =
      List.map
        (fun ((shadow_id, ty), arg) ->
          Sasgn (temp_name shadow_id, Some (strip_ref_and_const_type ty), arg) )
        non_trivial
    in
    let updates =
      List.map
        (fun ((shadow_id, _ty), _arg) ->
          Sexpr
            (CPPbinop
               ( "=",
                 CPPvar shadow_id,
                 CPPmove (CPPvar (temp_name shadow_id)) ) ) )
        non_trivial
    in
    temp_decls @ updates

(** Rewrite return statements inside a recursive visitor lambda. Base cases
    assign to [_result] and set [_continue = false]; recursive cases just update
    shadow params. Lambdas become void-returning. *)
let rec rewrite_lambda_return check varying shadow_params = function
  | Sreturn (Some (CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas])))
    when count_calls_expr check scrut = 0
         && List.exists
              (fun lambda ->
                match lambda with
                | CPPlambda (_, _, body, _) ->
                  collect_stmts check ~in_visitor:true body <> []
                | _ -> false )
              lambdas ->
    let rw = rewrite_lambda_return check varying shadow_params in
    let new_lambdas =
      map_visit_lambdas ~ret_ty:None
        ~rewrite:(fun _ body -> List.concat_map rw body) lambdas
    in
    make_visit_stmt scrut new_lambdas
  | Sreturn (Some e) ->
    ( match check e with
    | Some cs ->
      make_shadow_updates shadow_params (filter_by_mask varying cs.cs_args)
    | None -> assign_result_and_stop e )
  | Sif (cond, then_br, else_br) ->
    let rw = rewrite_lambda_return check varying shadow_params in
    [Sif (cond, List.concat_map rw then_br, List.concat_map rw else_br)]
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    let rw = rewrite_lambda_return check varying shadow_params in
    [
      Scustom_case
        ( ty,
          scrut,
          tyargs,
          List.map
            (fun (ps, ret_ty, body) -> (ps, ret_ty, List.concat_map rw body))
            branches,
          err );
    ]
  | Smatch (branches, default) ->
    let rw = rewrite_lambda_return check varying shadow_params in
    [
      Smatch
        ( List.map
            (fun br -> { br with smb_body = List.concat_map rw br.smb_body })
            branches,
          Option.map (List.concat_map rw) default );
    ]
  | Sblock stmts ->
    let rw = rewrite_lambda_return check varying shadow_params in
    [Sblock (List.concat_map rw stmts)]
  | s -> [s]

(** Rewrite a single statement for tail-call loopification.

    Handles three kinds of [Sreturn]:
    - {b Direct tail call} ([check] succeeds): replace with shadow variable
      updates wrapped in an [Sblock].  No [Scontinue] is emitted because the
      update block is always the terminal statement in its branch; control
      naturally falls through to the end of the [while] body and loops back.
    - {b Visit tail call}: rewrite the [std::visit] lambdas to update shadow
      variables (recursive branches) or set [_result] and [_continue = false]
      (base branches).
    - {b Direct base return}: assign [_result] and stop the loop.

    Branching statements ([Sif], [Sswitch], [Scustom_case], [Sblock]) delegate
    to {!rewrite_visit_stmts} for list-level rewriting, which also detects the
    void tail-call pattern ([Sexpr call; Sreturn None]). *)
let rec rewrite_visit_stmt check varying shadow_params = function
  | Sreturn (Some e) ->
    ( match check e with
    | Some cs ->
      (* Direct tail call — replace with shadow updates.  No Scontinue:
         the block is terminal in its branch, so control falls through
         to the while-loop test naturally. *)
      let assigns =
        make_shadow_updates shadow_params (filter_by_mask varying cs.cs_args)
      in
      Sblock assigns
    | None ->
    match e with
    | CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas]) ->
      let new_lambdas =
        List.map
          (fun lambda ->
            match lambda with
            | CPPlambda (lparams, _ret_ty, body, _capture) ->
              let has_rec = collect_stmts check ~in_visitor:true body <> [] in
              if has_rec then
                let new_body =
                  List.concat_map
                    (rewrite_lambda_return check varying shadow_params)
                    body
                in
                CPPlambda (lparams, None, new_body, false)
              else (* Base-case lambda: rewrite returns to assign _result *)
                let new_body =
                  List.concat_map
                    (rewrite_lambda_return check varying shadow_params)
                    body
                in
                CPPlambda (lparams, None, new_body, false)
            | e -> e )
          lambdas
      in
      Sexpr (make_visit_expr scrut new_lambdas)
    | _ ->
      (* Direct base return — assign _result and stop loop *)
      Sblock (assign_result_and_stop e) )
  | Sif (cond, then_br, else_br) ->
    let rw = rewrite_visit_stmts check varying shadow_params in
    Sif (cond, rw then_br, rw else_br)
  | Sswitch (scrut, r, branches, default) ->
    let rw = rewrite_visit_stmts check varying shadow_params in
    Sswitch
      (scrut, r, List.map (fun (id, body) -> (id, rw body)) branches, default)
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    let rw = rewrite_visit_stmts check varying shadow_params in
    Scustom_case
      ( ty,
        scrut,
        tyargs,
        List.map
          (fun (ps, ret_ty, body) -> (ps, ret_ty, rw body))
          branches,
        err )
  | Smatch (branches, default) ->
    let rw = rewrite_visit_stmts check varying shadow_params in
    Smatch
      ( List.map
          (fun br -> { br with smb_body = rw br.smb_body })
          branches,
        Option.map rw default )
  | Sblock stmts ->
    Sblock (rewrite_visit_stmts check varying shadow_params stmts)
  | s -> s

(** Rewrite a list of statements for tail-call loopification.

    In addition to delegating each statement to {!rewrite_visit_stmt}, this
    detects the void tail-call pattern:

    {v  Sexpr call; Sreturn None   (* call(); return; *)  v}

    which is semantically equivalent to [Sreturn (Some call)] — the call is
    in tail position even though C++ syntax splits it into two statements.
    This pattern is produced by [cofix_wrap] and [gen_stmts] for void
    cofixpoints and void-returning recursive functions. *)
and rewrite_visit_stmts check varying shadow_params = function
  | Sexpr e :: Sreturn _ :: rest when check e <> None ->
    (* Void tail-call (both [call(); return;] and [call(); return val;]):
       rewrite as [return call();].  The second form arises when the ITree
       unit continuation threads a [Unit::e_TT] return through the
       nat-match continuation rather than emitting a bare [return;]. *)
    rewrite_visit_stmt check varying shadow_params (Sreturn (Some e))
    :: rewrite_visit_stmts check varying shadow_params rest
  | s :: rest ->
    rewrite_visit_stmt check varying shadow_params s
    :: rewrite_visit_stmts check varying shadow_params rest
  | [] -> []

(** Returns true if the statement declares a new variable or type binding. *)
let declares_variable = function
  | Sdecl _ | Sdecl_init _ | Sstruct_def _ | Susing _ -> true
  | Sasgn (_, Some _, _) -> true (* typed assignment = declaration *)
  | _ -> false

(** Names declared directly by a statement (not recursing into sub-statements). *)
let direct_decl_ids = function
  | Sdecl (id, _) | Sdecl_init (id, _) -> [ id ]
  | Sasgn (id, Some _, _) -> [ id ]
  | Susing (id, _) -> [ id ]
  | _ -> []

(** Returns true if inlining [block_stmts] before [rest] at the same scope level
    would produce a duplicate declaration.  A conflict arises when a name first
    declared inside [block_stmts] also appears as a top-level declaration in
    [rest] (including inside [Sblock] nodes in [rest] that would themselves be
    inlined). *)
let would_conflict block_stmts rest =
  if not (List.exists declares_variable block_stmts) then false
  else
    let block_ids = List.concat_map direct_decl_ids block_stmts in
    let rest_ids =
      List.concat_map
        (function
          | Sblock ss -> List.concat_map direct_decl_ids ss
          | s -> direct_decl_ids s)
        rest
    in
    List.exists (fun id -> List.mem id rest_ids) block_ids

(** Remove unnecessary [Sblock] wrappers throughout a statement list.

    An [Sblock] wrapper is unnecessary — and can be inlined into the surrounding
    list — when doing so would not introduce a duplicate declaration at the
    enclosing scope level.  Concretely:

    - [Sblock []] is always dropped.
    - [Sblock stmts] is inlined when none of its declared names would clash with
      a name declared by any sibling statement in the enclosing list.  Since each
      [if]/[else]/[while] branch already provides its own [{}] scope in the emitted
      C++, inner blocks inside those branches are almost always safe to remove.

    Recurses into [Sif], [Sswitch], [Scustom_case], [Smatch], and [Swhile] so
    that blocks nested inside branches are also simplified. *)
let rec strip_unnecessary_blocks = function
  | Sblock stmts :: rest ->
    let inner' = strip_unnecessary_blocks stmts in
    let rest' = strip_unnecessary_blocks rest in
    ( match inner' with
    | [] -> rest'
    | _ when not (would_conflict inner' rest') -> inner' @ rest'
    | _ -> Sblock inner' :: rest' )
  | s :: rest -> strip_loopify_stmt s :: strip_unnecessary_blocks rest
  | [] -> []

(** Recursively strip unnecessary blocks from a single statement's sub-branches
    ([Sif], [Sswitch], [Scustom_case], [Smatch], [Swhile], nested [Sblock]). *)
and strip_loopify_stmt = function
  | Sif (cond, then_br, else_br) ->
    Sif
      ( cond,
        strip_unnecessary_blocks then_br,
        strip_unnecessary_blocks else_br )
  | Sswitch (scrut, r, branches, default) ->
    Sswitch
      ( scrut,
        r,
        List.map (fun (id, body) -> (id, strip_unnecessary_blocks body)) branches,
        Option.map strip_unnecessary_blocks default )
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    Scustom_case
      ( ty,
        scrut,
        tyargs,
        List.map
          (fun (ps, ret_ty, body) -> (ps, ret_ty, strip_unnecessary_blocks body))
          branches,
        err )
  | Smatch (branches, default) ->
    Smatch
      ( List.map
          (fun br -> { br with smb_body = strip_unnecessary_blocks br.smb_body })
          branches,
        Option.map strip_unnecessary_blocks default )
  | Swhile (cond, body) -> Swhile (cond, strip_unnecessary_blocks body)
  | Sblock stmts ->
    (* Reached when an Sblock appears as a non-first element inside another
       statement (rare; the list-level case above handles the common path). *)
    let stmts' = strip_unnecessary_blocks stmts in
    ( match stmts' with
    | [] -> Sblock []
    | [ s ] -> s
    | _ -> Sblock stmts' )
  | s -> s

(** Transform a tail-recursive function body into a [while] loop with shadow variables.

    Tail recursion is the simplest loopification case.  Since no work happens
    after the recursive call, we can convert it directly into iteration.

    {b Non-void functions} use a [_continue] guard variable and a [_result]
    accumulator:

    {v
    let rec f x = if base(x) then result else f(next(x))
    →
    T _result;
    auto _loop_x = x;
    bool _continue = true;
    while (_continue) {
      if (base(_loop_x)) { _result = result; _continue = false; }
      else { _loop_x = next(_loop_x); }
    }
    return _result;
    v}

    {b Void functions} (e.g. cofixpoint [spin], [forever]) never set
    [_continue = false] — their base cases exit via [return;] (which becomes
    [Sreturn None]) rather than assigning a result.  So [_continue] and
    [_result] are unnecessary and the loop simplifies to [while (true)]:

    {v
    CoFixpoint forever n := Tau (forever (S n))
    →
    auto _loop_n = n;
    while (true) { _loop_n = _loop_n + 1; }
    return;
    v}

    After rewriting, {!strip_empty_blocks} removes any empty [Sblock]s left
    by tail-call rewrites that produced no shadow updates (e.g. a
    zero-parameter cofixpoint like [spin] whose only recursive call has no
    arguments to update).

    @param param_inits Optional custom initializers for shadow variables
                       (default: copy from original parameter)
    @param check Call checker for identifying recursive calls
    @param pp_type Type pretty-printer (unused, kept for signature uniformity)
    @param params Function parameters [(id, type)] list
    @param ret_ty Return type of the function
    @param body Function body statements
    @return Transformed body with while loop structure *)
let transform_tail ?(param_inits = []) check _pp_type params ret_ty body =
  let varying = find_varying_params check params body in
  let varying_params = filter_by_mask varying params in
  let shadow_params =
    List.map (fun (id, ty) -> (shadow_name id, ty)) varying_params
  in
  let subs =
    List.map2 (fun (id, _) (sid, _) -> (id, sid)) varying_params shadow_params
  in
  let is_void = ret_ty = Tvoid in
  (* Shadow variable declarations (only for varying params) *)
  let shadow_decls =
    List.map2
      (fun (orig_id, ty) (shadow_id, _) ->
        let init_expr =
          match List.assoc_opt orig_id param_inits with
          | Some custom -> custom
          | None ->
            if is_moveable_param_type ty then CPPmove (CPPvar orig_id)
            else CPPvar orig_id
        in
        Sasgn (shadow_id, Some (strip_ref_and_const_type ty), init_expr) )
      varying_params
      shadow_params
  in
  (* Substitute param references in body *)
  let body' = List.map (subst_stmt subs) body in
  (* Rewrite recursive calls (list-level rewrite handles void tail-call
     pattern [Sexpr call; Sreturn None] → [Sreturn (Some call)]) *)
  let body'' =
    rewrite_visit_stmts check varying shadow_params body'
  in
  let body'' = strip_unnecessary_blocks body'' in
  (* Assemble the loop body.
     - Non-void: [T _result; ... while (true) { ... break; } return _result;]
     - Void:     [... while (true) { ... } return;]
     Non-void base cases exit via [Sbreak] (from [assign_result_and_stop]).
     Void base cases exit via [Sreturn None] (plain [return;]).
     Both use [while (true)] for the loop condition. *)
  (if is_void then [] else [Sdecl (Id.of_string "_result", ret_ty)])
  @ shadow_decls
  @ [
      Swhile (CPPbool true, body'');
      (if is_void then Sreturn None else
       Sreturn (Some (CPPvar (Id.of_string "_result"))));
    ]

(* {2 Non-tail recursion transformation}

   For non-tail recursive functions, we use an explicit stack of std::function
   continuations stored in a vector.

   Single non-tail: each recursive branch pushes a continuation that captures
   the pre-computed values, then updates the loop parameter to the recursive
   argument. After the loop, the continuations are applied in reverse order to
   build the final result.

   Double non-tail: uses a frame-based stack with Enter/After/Combine variants
   and a std::visit-based while loop. See [transform_multi]. *)

(** {3 Double-call decomposition for multi-recursive functions}

    Decompose expressions with exactly 2 recursive calls, like
    [fib(p) + fib(m)], into the two call argument lists and a combining
    operation. *)

type double_decomp = {
  dd_first_args : cpp_expr list;
  dd_second_args : cpp_expr list;
  dd_saved : cpp_expr list;
      (** Non-recursive expressions to save for combine *)
  dd_combine : cpp_expr list -> cpp_expr -> cpp_expr -> cpp_expr;
      (** [dd_combine saved_vars left_result right_result] *)
}

(** Check whether any return expression in [body] has at least [n] recursive
    calls. Used to distinguish single-call, double-call, and triple-call patterns.

    @param n Minimum number of recursive calls to look for
    @param check The call checker to identify recursive calls
    @param body The function body to search *)
let has_n_call_expr n check body =
  (* Do NOT recurse into [Smatch] (or [Scustom_case]) branches: they represent
     type dispatch (pattern matching on an inductive), where each branch's
     recursive calls are independent.  The old [CPPvisit] code didn't count
     calls inside visit lambdas, so [Smatch] must be treated the same way.
     Without this, functions with 2 recursive calls in a single match branch
     (e.g. tree map) are incorrectly classified as multi-recursive instead of
     being handled by [transform_nontail]. *)
  let rec check_stmt = function
    | Sreturn (Some e) -> count_calls_expr check e >= n
    | Sif (_, then_br, else_br) ->
      List.exists check_stmt then_br || List.exists check_stmt else_br
    | Sblock stmts -> List.exists check_stmt stmts
    | Sswitch (_, _, branches, _) ->
      List.exists (fun (_, body) -> List.exists check_stmt body) branches
    | _ -> false
  in
  List.exists check_stmt body

(** Check whether any return has 2+ recursive calls (multi-recursion). *)
let has_multi_call_expr check body = has_n_call_expr 2 check body

let has_higher_order_template_param tparams =
  List.exists
    (function
      | TTfun _ | TTconcept _ -> true
      | _ -> false )
    (List.map fst tparams)

(** {3 Expression decomposition}

    Analyze a return expression to find how the recursive call result is used.
    We decompose [return wrapper(args..., RECURSE(rec_args))] into:
    - [saved_exprs]: expressions to evaluate before recursing (stored in frame)
    - [rec_args]: arguments to the recursive call
    - [rebuild]: how to reconstruct the result from saved values and recursive
      result *)

(** Represents a decomposed non-tail recursive return expression. The recursive
    call's result is combined with saved values via [rebuild]. *)
type decomposed = {
  d_saved : cpp_expr list;
      (** Expressions to evaluate and save before recursing *)
  d_saved_types : cpp_type list;
      (** Types of saved expressions (for frame struct fields) *)
  d_rec_args : cpp_expr list;  (** Arguments to pass to the recursive call *)
  d_rebuild : cpp_expr list -> cpp_expr -> cpp_expr;
      (** [d_rebuild saved_vars result] reconstructs the final expression.
          [saved_vars] are CPPvar references to the saved values; [result] is
          the recursive call's result. *)
}

(** {3 Tail Modulo Cons (TMC)}

    When a non-tail recursive call appears nested inside one or more constructor
    factories (e.g., [Cons_(x, RECURSE(xs))] or
    [Cons_(x, Cons_(x, RECURSE(xs)))]), the function can be optimized using
    destination-passing style: allocate the constructor cells immediately with
    [nullptr] holes, link them together, then fill the innermost hole on the
    next iteration.  This achieves O(1) extra space instead of O(n) frame stack.

    See Bour, Clément, Scherer 2021 — "Tail Modulo Cons". *)

(** One constructor cell allocation in a (possibly nested) TMC chain.
    For [cons x (cons x (stutter xs))], the outer [cons x _] and inner
    [cons x _] are each represented by one [tmc_cell_alloc]. *)
type tmc_cell_alloc = {
  tca_factory : cpp_expr;
      (** Constructor factory function, e.g., [list<T>::ctor::Cons_] *)
  tca_type_expr : cpp_expr;
      (** The type expression before [::ctor], e.g., [list<T>] *)
  tca_ctor_name : string;
      (** Constructor name without trailing underscore, e.g., ["Cons"] *)
  tca_rec_field_idx : int;
      (** Index of the recursive argument in the constructor args *)
  tca_non_rec_args : (int * cpp_expr) list;
      (** [(index, expr)] for non-recursive arguments *)
  tca_n_args : int;
      (** Total number of constructor arguments *)
  tca_uptr_field_idxs : int list;
      (** Field indices that are stored as [unique_ptr] in the struct
          (self-referencing fields).  Used by {!build_cell_call} to
          wrap value-type args in [make_unique] for direct struct construction. *)
}

(** Information about a single TMC-eligible branch: a return expression of the
    form [CtorFactory(... CtorFactory(non_rec_args, RECURSE(rec_args)) ...)].
    The cell list is outermost-first, innermost-last. *)
type tmc_branch_info = {
  tmc_cells : tmc_cell_alloc list;
      (** Constructor cells, outermost first, innermost last *)
  tmc_rec_args : cpp_expr list;
      (** Arguments to the innermost recursive call *)
}

(** Summary of TMC analysis for a whole function.  The type is a unit-like
    marker: [Some ()] signals that all TMC branches are eligible and use the
    same constructor and recursive field.  The per-branch details are carried
    directly in the [tmc_cell_alloc] records inside each [tmc_branch]. *)
type tmc_info = unit [@@warning "-34"]

(** Try to decompose an expression with exactly one recursive call. Returns
    [Some decomposed] if successful, [None] otherwise.

    Handles patterns like:
    - [Cons_(f(x), RECURSE(xs))] — constructor wrapping
    - [n * RECURSE(m)] — binary operator
    - [n + RECURSE(m)] — arithmetic *)
let rec decompose_single_call check expr =
  match check expr with
  | Some _cs ->
    (* The expression IS the recursive call — this is a tail call, not our
       concern here. Return None to let the caller handle it. *)
    None
  | None ->
  match expr with
  (* Binary operator: e1 OP RECURSE or RECURSE OP e2 *)
  | CPPbinop (op, e1, e2) ->
    let c1 = count_calls_expr check e1 in
    let c2 = count_calls_expr check e2 in
    if c1 = 0 && c2 = 1 then
      (* e1 OP RECURSE(e2) — recurse on right *)
        match
          decompose_single_call check e2
        with
      | Some d ->
        Some
          {
            d with
            d_saved = e1 :: d.d_saved;
            d_saved_types = Tunknown :: d.d_saved_types;
            d_rebuild =
              (fun saved result ->
                let e1' = List.hd saved in
                let inner = d.d_rebuild (List.tl saved) result in
                CPPbinop (op, e1', inner) );
          }
      | None ->
      (* Direct: e1 OP recurse(args) *)
      match check e2 with
      | Some cs ->
        Some
          {
            d_saved = [e1];
            d_saved_types = [Tunknown];
            d_rec_args = cs.cs_args;
            d_rebuild =
              (fun saved result -> CPPbinop (op, List.hd saved, result));
          }
      | None -> None
    else if c1 = 1 && c2 = 0 then
      (* RECURSE(e1) OP e2 — recurse on left *)
        match
          decompose_single_call check e1
        with
      | Some d ->
        Some
          {
            d with
            d_saved = d.d_saved @ [e2];
            d_saved_types = d.d_saved_types @ [Tunknown];
            d_rebuild =
              (fun saved result ->
                let n = List.length d.d_saved in
                let d_saved = List.filteri (fun i _ -> i < n) saved in
                let e2' = List.nth saved n in
                let inner = d.d_rebuild d_saved result in
                CPPbinop (op, inner, e2') );
          }
      | None ->
      match check e1 with
      | Some cs ->
        Some
          {
            d_saved = [e2];
            d_saved_types = [Tunknown];
            d_rec_args = cs.cs_args;
            d_rebuild =
              (fun saved result -> CPPbinop (op, result, List.hd saved));
          }
      | None -> None
    else
      None
  (* Function call with recursive argument *)
  | CPPfun_call (f, args) when count_calls_expr check f = 0 ->
    decompose_funcall check f args
  (* Method call: obj.method(args) where obj has the recursive call *)
  | CPPmethod_call (obj, method_id, margs)
    when count_calls_expr check obj >= 1
         && List.for_all (fun a -> count_calls_expr check a = 0) margs ->
    ( match decompose_single_call check obj with
    | Some d ->
      let n_d = List.length d.d_saved in
      Some
        {
          d with
          d_saved = d.d_saved @ margs;
          d_saved_types = d.d_saved_types @ List.map (fun _ -> Tunknown) margs;
          d_rebuild =
            (fun saved result ->
              let d_saved = List.filteri (fun i _ -> i < n_d) saved in
              let method_args = List.filteri (fun i _ -> i >= n_d) saved in
              CPPmethod_call (d.d_rebuild d_saved result, method_id, method_args) );
        }
    | None ->
    match check obj with
    | Some cs ->
      Some
        {
          d_saved = margs;
          d_saved_types = List.map (fun _ -> Tunknown) margs;
          d_rec_args = cs.cs_args;
          d_rebuild =
            (fun saved result -> CPPmethod_call (result, method_id, saved));
        }
    | None -> None )
  (* Move wrapping a recursive expression *)
  | CPPmove inner ->
    ( match decompose_single_call check inner with
    | Some d ->
      Some {d with d_rebuild = (fun saved r -> CPPmove (d.d_rebuild saved r))}
    | None -> None )
  | _ -> None

(** Decompose a function call [f(a0, a1, ..., an)] where exactly one argument
    contains the recursive call. *)
and decompose_funcall check f args =
  (* Find which argument has the recursive call *)
  let rec_indices =
    List.mapi (fun i a -> (i, count_calls_expr check a)) args
    |> List.filter (fun (_, c) -> c > 0)
  in
  match rec_indices with
  | [(rec_idx, 1)] ->
    (* Exactly one argument has exactly one recursive call *)
    let rec_arg = List.nth args rec_idx in
    let non_rec_args =
      List.mapi (fun i a -> (i, a)) args
      |> List.filter (fun (i, _) -> i <> rec_idx)
      |> List.map snd
    in
    ( match decompose_single_call check rec_arg with
    | Some d ->
      (* The recursive call is nested deeper *)
      let n_saved_before = List.length non_rec_args in
      Some
        {
          d with
          d_saved = non_rec_args @ d.d_saved;
          d_saved_types =
            List.map (fun _ -> Tunknown) non_rec_args @ d.d_saved_types;
          d_rebuild =
            (fun saved result ->
              let outer_saved =
                List.filteri (fun i _ -> i < n_saved_before) saved
              in
              let inner_saved =
                List.filteri (fun i _ -> i >= n_saved_before) saved
              in
              let inner = d.d_rebuild inner_saved result in
              let new_args =
                List.init (List.length args) (fun i ->
                  if i = rec_idx then
                    inner
                  else
                    let pos = if i < rec_idx then i else i - 1 in
                    List.nth outer_saved pos )
              in
              CPPfun_call (f, new_args) );
        }
    | None ->
    (* Direct: f(non_rec..., RECURSE(args), non_rec...) *)
    match check rec_arg with
    | Some cs ->
      Some
        {
          d_saved = non_rec_args;
          d_saved_types = List.map (fun _ -> Tunknown) non_rec_args;
          d_rec_args = cs.cs_args;
          d_rebuild =
            (fun saved result ->
              let new_args =
                List.init (List.length args) (fun i ->
                  if i = rec_idx then
                    result
                  else
                    let pos = if i < rec_idx then i else i - 1 in
                    List.nth saved pos )
              in
              CPPfun_call (f, new_args) );
        }
    | None -> None )
  | _ -> None

(** Decompose an expression with exactly 2 recursive calls. Handles binary
    operators [e1 + e2] and function calls [f(a0, ..., an)] where exactly 2
    arguments contain recursive calls. Supports both direct calls and calls
    nested inside constructors/wrappers via [decompose_single_call]. *)
and decompose_double_call check expr =
  (* Extract a single-call decomposition, treating direct calls as trivial. *)
  let get_decomp e =
    match check e with
    | Some cs ->
      Some
        {
          d_saved = [];
          d_saved_types = [];
          d_rec_args = cs.cs_args;
          d_rebuild = (fun _saved result -> result);
        }
    | None -> decompose_single_call check e
  in
  (* Try to decompose two subexpressions each with 1 recursive call. *)
  let try_pair e1 e2 mk_combine =
    let c1 = count_calls_expr check e1 in
    let c2 = count_calls_expr check e2 in
    if c1 = 1 && c2 = 1 then
      match
        (get_decomp e1, get_decomp e2)
      with
      | Some dec1, Some dec2 ->
        Some
          {
            dd_first_args = dec1.d_rec_args;
            dd_second_args = dec2.d_rec_args;
            dd_saved = dec1.d_saved @ dec2.d_saved;
            dd_combine =
              (fun saved left right ->
                let n1 = List.length dec1.d_saved in
                let saved1 = List.filteri (fun i _ -> i < n1) saved in
                let saved2 = List.filteri (fun i _ -> i >= n1) saved in
                let rebuilt_left = dec1.d_rebuild saved1 left in
                let rebuilt_right = dec2.d_rebuild saved2 right in
                mk_combine rebuilt_left rebuilt_right );
          }
      | _ -> None
    else
      None
  in
  match expr with
  | CPPbinop (op, e1, e2) ->
    let c1 = count_calls_expr check e1 in
    let c2 = count_calls_expr check e2 in
    if c1 >= 1 && c2 >= 1 then
      try_pair e1 e2 (fun left right -> CPPbinop (op, left, right))
    else if c1 = 0 && c2 >= 2 then
      match
        decompose_double_call check e2
      with
      | Some dd ->
        Some
          {
            dd with
            dd_saved = e1 :: dd.dd_saved;
            dd_combine =
              (fun saved l r ->
                let e1' = List.hd saved in
                CPPbinop (op, e1', dd.dd_combine (List.tl saved) l r) );
          }
      | None -> None
    else if c1 >= 2 && c2 = 0 then
      match
        decompose_double_call check e1
      with
      | Some dd ->
        Some
          {
            dd with
            dd_saved = dd.dd_saved @ [e2];
            dd_combine =
              (fun saved l r ->
                let n = List.length saved - 1 in
                let inner_saved = List.filteri (fun i _ -> i < n) saved in
                let e2' = List.nth saved n in
                CPPbinop (op, dd.dd_combine inner_saved l r, e2') );
          }
      | None -> None
    else
      None
  | CPPfun_call (f, args) when count_calls_expr check f = 0 ->
    let arg_calls = List.mapi (fun i a -> (i, count_calls_expr check a)) args in
    let rec_indices = List.filter (fun (_, c) -> c > 0) arg_calls in
    let rebuild_funcall
        i1
        i2
        non_rec_indexed
        saved_offset
        dd_inner
        saved
        left
        right =
      (* Reconstruct f(args) with rec results at positions i1, i2 *)
      let inner =
        dd_inner (List.filteri (fun i _ -> i < saved_offset) saved) left right
      in
      let outer_saved = List.filteri (fun i _ -> i >= saved_offset) saved in
      let new_args =
        List.init (List.length args) (fun i ->
          if i = i1 then
            match
              inner
            with
            | CPPbinop ("__dd_pair__", l, _) -> l
            | x -> x
          else if i = i2 then
            match
              inner
            with
            | CPPbinop ("__dd_pair__", _, r) -> r
            | x -> x
          else
            let pos =
              List.filter (fun (j, _) -> j < i) non_rec_indexed |> List.length
            in
            List.nth outer_saved pos )
      in
      CPPfun_call (f, new_args)
    in
    ( match rec_indices with
    | [(i1, c1); (i2, c2)] when c1 = 1 && c2 = 1 ->
      let e1 = List.nth args i1 in
      let e2 = List.nth args i2 in
      let non_rec_indexed =
        List.mapi (fun i _ -> (i, ())) args
        |> List.filter (fun (i, _) -> i <> i1 && i <> i2)
      in
      let non_rec_args =
        List.map (fun (i, _) -> List.nth args i) non_rec_indexed
      in
      ( match
          try_pair e1 e2 (fun left right ->
            CPPbinop ("__dd_pair__", left, right) )
        with
      | Some dd ->
        let saved_offset = List.length dd.dd_saved in
        Some
          {
            dd with
            dd_saved = dd.dd_saved @ non_rec_args;
            dd_combine =
              (fun saved left right ->
                rebuild_funcall
                  i1
                  i2
                  non_rec_indexed
                  saved_offset
                  dd.dd_combine
                  saved
                  left
                  right );
          }
      | None -> None )
    | [(i1, c)] when c = 2 ->
      let inner = List.nth args i1 in
      ( match decompose_double_call check inner with
      | Some dd ->
        let non_rec_indexed =
          List.mapi (fun i _ -> (i, ())) args
          |> List.filter (fun (i, _) -> i <> i1)
        in
        let non_rec_args =
          List.map (fun (i, _) -> List.nth args i) non_rec_indexed
        in
        let saved_offset = List.length dd.dd_saved in
        Some
          {
            dd with
            dd_saved = dd.dd_saved @ non_rec_args;
            dd_combine =
              (fun saved l r ->
                let inner_saved =
                  List.filteri (fun i _ -> i < saved_offset) saved
                in
                let outer_saved =
                  List.filteri (fun i _ -> i >= saved_offset) saved
                in
                let inner_result = dd.dd_combine inner_saved l r in
                let new_args =
                  List.init (List.length args) (fun i ->
                    if i = i1 then
                      inner_result
                    else
                      let pos =
                        List.filter (fun (j, _) -> j < i) non_rec_indexed
                        |> List.length
                      in
                      List.nth outer_saved pos )
                in
                CPPfun_call (f, new_args) );
          }
      | None -> None )
    | _ -> None )
  | CPPmove inner ->
    ( match decompose_double_call check inner with
    | Some dd ->
      Some
        {
          dd with
          dd_combine = (fun saved l r -> CPPmove (dd.dd_combine saved l r));
        }
    | None -> None )
  | _ -> None

(** Check whether any return has 3+ recursive calls (triple-recursion). *)
let has_triple_call_expr check body = has_n_call_expr 3 check body

(** {3 TMC detection}

    Analyze function bodies to detect the Tail-Modulo-Cons pattern:
    non-tail recursive calls nested inside one or more constructor factories. *)

(** Test whether an expression is a constructor factory call, i.e.,
    [Type::cons(args)].  Returns [(type_expr, ctor_name, factory_name, args)]
    where [type_expr] is the base type (e.g., [list<T>]), [ctor_name] is the
    constructor struct name (e.g., ["Cons"]), [factory_name] is the factory
    method name (e.g., ["cons"]), and [args] are the constructor arguments.

    Factory calls are the only use of [CPPfun_call(CPPqualified(...), ...)]
    in the MiniCpp AST.  The struct name is the capitalized factory name. *)
let is_ctor_factory_call = function
  | CPPfun_call (CPPqualified (type_expr, factory_id), args) ->
    let factory_s = Id.to_string factory_id in
    let n = String.length factory_s in
    (* Skip built-in accessors and other non-factory qualified calls *)
    if factory_s = "v" || factory_s = "v_mut" || factory_s = "lazy_"
    then None
    else
      (* Strip trailing underscore (collision escape) before capitalizing *)
      let base =
        if n > 0 && factory_s.[n - 1] = '_' then
          String.sub factory_s 0 (n - 1)
        else factory_s
      in
      let struct_name = String.capitalize_ascii base in
      Some (type_expr, struct_name, factory_s, args)
  | _ -> None

(** Try to decompose a return expression as a TMC-eligible branch.  Handles
    both single-level ([cons x (RECURSE xs)]) and nested constructors
    ([cons x (cons x (RECURSE xs))]).  Strips [CPPmove] wrapping before
    checking.

    {b Example.}  Given [cons x (cons y (f xs))]:
    - Outer constructor [cons(x, HOLE)] is cell 0 (allocated first, returned to
      the caller via [_head]).
    - Inner constructor [cons(y, HOLE)] is cell 1 (allocated second, linked
      into cell 0's recursive field).
    - [f xs] is the recursive call that fills cell 1's HOLE.

    Cells are returned outermost-first so the caller can chain them:
    allocate cell 0, allocate cell 1, link cell 1 into cell 0, then loop with
    [_last] pointing to cell 1 for the next iteration to fill.

    @return [Some tmc_branch_info] with a chain of cells, outermost first *)
let rec try_tmc_decompose check expr =
  let expr' = match expr with CPPmove e -> e | e -> e in
  match is_ctor_factory_call expr' with
  | None -> None
  | Some (type_expr, ctor_name, factory_s, args) ->
    let n_args = List.length args in
    let indexed = List.mapi (fun i a -> (i, a)) args in
    let non_rec_of idx =
      List.filter_map
        (fun (i, a) -> if i <> idx then Some (i, a) else None)
        indexed
    in
    let make_cell idx = {
      tca_factory =
        CPPqualified (type_expr, Id.of_string factory_s);
      tca_type_expr = type_expr;
      tca_ctor_name = ctor_name;
      tca_rec_field_idx = idx;
      tca_non_rec_args = non_rec_of idx;
      tca_n_args = n_args;
      tca_uptr_field_idxs = [idx];
    } in
    (* Find which args are direct recursive calls *)
    let direct =
      List.filter_map
        (fun (i, a) ->
          match check a with Some cs -> Some (i, cs) | None -> None)
        indexed
    in
    ( match direct with
    | [(idx, cs)] ->
      (* Single direct recursive call — innermost cell *)
      Some { tmc_cells = [make_cell idx]; tmc_rec_args = cs.cs_args }
    | [] ->
      (* No direct call — look for a nested constructor wrapping a call *)
      let nested =
        List.filter_map
          (fun (i, a) ->
            if count_calls_expr check a = 1 then Some (i, a) else None)
          indexed
      in
      ( match nested with
      | [(idx, nested_expr)] ->
        ( match try_tmc_decompose check nested_expr with
        | Some inner ->
          Some { tmc_cells = make_cell idx :: inner.tmc_cells;
                 tmc_rec_args = inner.tmc_rec_args }
        | None -> None )
      | _ -> None )
    | _ -> None (* Multiple direct calls — not TMC *) )

(** Classify an entire function body for TMC eligibility.  Walks all return
    positions (including inside [std::visit] lambda bodies) and checks that:
    - Every return is either a tail call, a base case (0 recursive calls), or a
      TMC-eligible constructor wrapping
    - All TMC branches use the {e same} constructor name and recursive field

    @return [Some tmc_info] if the function is TMC-eligible *)
let try_tmc_classify check body =
  let tmc_branches = ref [] in
  let compatible = ref true in
  (* Scan a single return expression *)
  let scan_return_expr e =
    if not !compatible then ()
    else
      match check e with
      | Some _ -> () (* tail call — compatible *)
      | None ->
        let n = count_calls_expr check e in
        if n = 0 then () (* base case *)
        else if n = 1 then (
          match try_tmc_decompose check e with
          | Some br -> tmc_branches := br :: !tmc_branches
          | None -> compatible := false )
        else compatible := false
  in
  (* Scan returns inside a lambda body (may contain nested visits) *)
  let rec scan_lambda_body stmts =
    List.iter scan_lambda_stmt stmts
  and scan_lambda_stmt = function
    | Sreturn (Some (CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas])))
      when count_calls_expr check scrut = 0 ->
      List.iter
        (fun lambda ->
          match lambda with
          | CPPlambda (_, _, body, _) -> scan_lambda_body body
          | _ -> () )
        lambdas
    | Sreturn (Some e) -> scan_return_expr e
    | Sif (_, then_br, else_br) ->
      scan_lambda_body then_br;
      scan_lambda_body else_br
    | Scustom_case (_, _, _, branches, _) ->
      List.iter (fun (_, _, body) -> scan_lambda_body body) branches
    | Sswitch (_, _, branches, _) ->
      List.iter (fun (_, body) -> scan_lambda_body body) branches
    | Smatch (branches, default) ->
      List.iter (fun br ->
        ( match br.smb_reuse with
        | Some (_, _, stmts) -> scan_lambda_body stmts
        | None -> () );
        scan_lambda_body br.smb_body) branches;
      (match default with Some ss -> scan_lambda_body ss | None -> ())
    | Sblock stmts -> scan_lambda_body stmts
    | _ -> ()
  in
  (* Scan top-level statements *)
  let rec scan_stmt = function
    | Sreturn (Some (CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas])))
      when count_calls_expr check scrut = 0 ->
      List.iter
        (fun lambda ->
          match lambda with
          | CPPlambda (_, _, body, _) -> scan_lambda_body body
          | _ -> () )
        lambdas
    | Sreturn (Some e) -> scan_return_expr e
    | Sif (_, then_br, else_br) ->
      List.iter scan_stmt then_br;
      List.iter scan_stmt else_br
    | Scustom_case (_, _, _, branches, _) ->
      List.iter (fun (_, _, body) -> List.iter scan_stmt body) branches
    | Sswitch (_, _, branches, _) ->
      List.iter (fun (_, body) -> List.iter scan_stmt body) branches
    | Smatch (branches, default) ->
      List.iter (fun br ->
        ( match br.smb_reuse with
        | Some (_, _, stmts) -> List.iter scan_stmt stmts
        | None -> () );
        List.iter scan_stmt br.smb_body) branches;
      (match default with Some ss -> List.iter scan_stmt ss | None -> ())
    | Sblock stmts -> List.iter scan_stmt stmts
    | _ -> ()
  in
  List.iter scan_stmt body;
  if not !compatible || !tmc_branches = [] then None
  else
    let branches = !tmc_branches in
    let first = List.hd branches in
    (* All branches must use the same innermost constructor and recursive
       field — the innermost cell determines _head/_last type and patching. *)
    let inner br = List.rev br.tmc_cells |> List.hd in
    let first_inner = inner first in
    let all_same =
      List.for_all
        (fun br ->
          let i = inner br in
          i.tca_ctor_name = first_inner.tca_ctor_name
          && i.tca_rec_field_idx = first_inner.tca_rec_field_idx )
        branches
    in
    if all_same then Some ()
    else None

(** {3 TMC transformation}

    Converts non-tail recursive functions where the recursive call is wrapped
    in one or more constructors (e.g., [cons x (f xs)] or
    [cons x (cons x (f xs))]) into iterative loops that build the result
    top-down using destination-passing style.

    Instead of an O(n) frame stack, TMC uses O(1) extra space by allocating
    constructor cells immediately with [nullptr] holes, linking nested cells
    together, then filling the innermost hole on the next iteration.

    Single-cell example ([cons x (f xs)]):
    {[
      auto _cell = Cons_(x, nullptr);
      <patch _head/_last with _cell>
      _last = _cell;
    ]}

    Nested-cell example ([cons x (cons x (f xs))]):
    {[
      auto _cell  = Cons_(x, nullptr);   // outer
      auto _cell1 = Cons_(x, nullptr);   // inner
      _cell.tail  = _cell1;              // link
      <patch _head/_last with _cell>
      _last = _cell1;                    // advance to innermost
    ]} *)

(** Generate [std::get<typename Type::Ctor>(ptr->v_mut()).<field> = val] —
    the statement that patches the recursive field of a TMC cell.

    The field index accounts for the reversed AST argument order
    (see translation.ml:1776): AST index [rec_field_idx] maps to struct
    field index [n_args - 1 - rec_field_idx].  The actual field name is
    resolved via {!Common.lookup_ctor_field_name}, which returns the
    descriptive Rocq binder name (e.g. [d_tl]) when one was registered
    during inductive definition, or falls back to the positional name
    [d_a{idx}]. *)
let patch_cell_field pp_expr ~type_expr ~ctor_name ~n_args ~rec_field_idx
    ptr val_expr =
  let field_idx = n_args - 1 - rec_field_idx in
  let field_id = Common.lookup_ctor_field_name ctor_name field_idx in
  let type_str = pp_expr type_expr in
  let get_expr =
    CPPraw ("std::get<typename " ^ type_str ^ "::" ^ ctor_name ^ ">")
  in
  let v_mut = CPPmethod_call (ptr, Id.of_string "v_mut", []) in
  Sassign_field (CPPfun_call (get_expr, [v_mut]), field_id, val_expr)

(** Generate the if/else that links a value into the TMC chain.  On the first
    iteration, assigns to [_head]; on subsequent iterations, patches the
    recursive field of the last allocated cell via {!patch_cell_field}.

    {[
      if (_last) \{
        std::get<typename Type::Ctor>(_last->v_mut()).d_aN = val;
      \} else \{
        _head = val;
      \}
    ]} *)
let patch_tmc_dest ~vt_ret _pp_expr _ti val_expr =
  (* Write-pointer technique: *_write = val.
     _write always points to where the next value should go — initially
     &_head, then the recursive field of the most recently allocated cell.
     No branch needed: the pointer handles both the first-element and
     subsequent-element cases uniformly.
     For value-type returns, base-case values need make_unique wrapping;
     cell values (from build_cell_call) are already unique_ptr. *)
  let val_expr =
    match vt_ret with
    | Some _ -> CPPmove val_expr
    | None -> val_expr
  in
  [Sexpr (CPPbinop ("=", CPPderef (CPPvar (Id.of_string "_write")), val_expr))]

(** Wrap a base-case value in [make_unique] for value-type returns.
    TMC branch cells are already [unique_ptr] from {!build_cell_call}. *)
let wrap_base_for_vt vt_ret val_expr =
  match vt_ret with
  | Some ret_ty ->
    CPPfun_call (CPPmk_unique ret_ty, [val_expr])
  | None -> val_expr

(** Build a constructor call with [nullptr] at the recursive argument position.

    When [~vt_ret] is [Some ret_ty], the factory method cannot accept [nullptr]
    because the recursive parameter is a value type.  Instead we construct the
    inner struct directly and wrap it:
    [std::make_unique<list<T>>(typename list<T>::Cons\{x, nullptr\})]

    @param cell A single TMC cell allocation descriptor
    @param vt_ret [Some ret_ty] for value-type returns, [None] otherwise *)
let build_cell_call ~vt_ret pp_expr cell =
  let args =
    List.init cell.tca_n_args (fun i ->
      if i = cell.tca_rec_field_idx then CPPraw "nullptr"
      else
        match List.assoc_opt i cell.tca_non_rec_args with
        | Some e ->
          (* For value-type return, non-rec args at unique_ptr field positions
             need wrapping in make_unique.  The struct field is unique_ptr<T>
             but the factory-produced value is bare T. *)
          if vt_ret <> None && List.mem i cell.tca_uptr_field_idxs then
            (match vt_ret with
             | Some ret_ty -> CPPfun_call (CPPmk_unique ret_ty, [e])
             | None -> e)
          else e
        | None ->
          (* This shouldn't happen if the analysis is correct *)
          CPPraw "std::any{}" )
  in
  match vt_ret with
  | Some ret_ty ->
    (* Direct struct construction wrapped in make_unique:
       std::make_unique<Type>(typename Type::Ctor{args...}) *)
    let type_str = pp_expr cell.tca_type_expr in
    let struct_init =
      CPPraw ("typename " ^ type_str ^ "::" ^ cell.tca_ctor_name)
    in
    CPPfun_call (CPPmk_unique ret_ty,
                 [CPPfun_call (struct_init, args)])
  | None ->
    CPPfun_call (cell.tca_factory, args)

(** Generate statements for a TMC branch with possibly nested constructor cells.
    Allocates all cells with [nullptr] holes, links consecutive pairs via
    {!patch_cell_field}, patches the destination with the outermost cell, and
    sets [_last] to the innermost.

    For a single cell (v1 behaviour), emits the same code as before.
    For nested cells (e.g., [cons x (cons x (RECURSE xs))]), emits:
    {[
      auto _cell  = Cons_(x, nullptr);    // outer
      auto _cell1 = Cons_(x, nullptr);    // inner
      outer.tail = _cell1;                // link
      <patch _head/_last with _cell>      // destination
      _last = _cell1;                     // advance
      <shadow updates>
    ]} *)
let build_tmc_branch_stmts ~vt_ret pp_expr ti br varying shadow_params =
  (* Generate unique cell names: _cell, _cell1, _cell2, ... *)
  let cell_names =
    List.mapi
      (fun i _ ->
        Id.of_string (if i = 0 then "_cell" else "_cell" ^ string_of_int i))
      br.tmc_cells
  in
  (* 1. Allocate all cells with nullptr holes *)
  let cell_decls =
    List.map2
      (fun cell_id cell ->
        Sasgn (cell_id, Some Tauto, build_cell_call ~vt_ret pp_expr cell))
      cell_names br.tmc_cells
  in
  (* 2. Link consecutive cells: outer.rec_field = inner *)
  let rec link_cells cells names =
    match cells, names with
    | cell :: rest_cells, outer_name :: (inner_name :: _ as rest_names) ->
      patch_cell_field pp_expr
        ~type_expr:cell.tca_type_expr ~ctor_name:cell.tca_ctor_name
        ~n_args:cell.tca_n_args ~rec_field_idx:cell.tca_rec_field_idx
        (CPPvar outer_name)
        (match vt_ret with
         | Some _ -> CPPmove (CPPvar inner_name)
         | None -> CPPvar inner_name)
      :: link_cells rest_cells rest_names
    | _ -> []
  in
  let link_stmts = link_cells br.tmc_cells cell_names in
  (* 3. Patch destination with outermost cell via write pointer *)
  let patch = patch_tmc_dest ~vt_ret pp_expr ti (CPPvar (List.hd cell_names)) in
  (* 4. Advance _write to the recursive field of the innermost cell.
        Generates: _write = &std::get<typename Type::Ctor>(inner->v_mut()).field; *)
  let inner_ti = List.rev br.tmc_cells |> List.hd in
  let field_idx = inner_ti.tca_n_args - 1 - inner_ti.tca_rec_field_idx in
  let field_id = Common.lookup_ctor_field_name inner_ti.tca_ctor_name field_idx in
  let update_write =
    match vt_ret with
    | Some _ ->
      let rec ptr_to_cell current_ptr = function
        | [] | [_] -> current_ptr
        | cell :: rest ->
          let field_idx = cell.tca_n_args - 1 - cell.tca_rec_field_idx in
          let field_id = Common.lookup_ctor_field_name cell.tca_ctor_name field_idx in
          let type_str = pp_expr cell.tca_type_expr in
          let field =
            "std::get<typename " ^ type_str ^ "::" ^ cell.tca_ctor_name
            ^ ">(" ^ current_ptr ^ "->v_mut())." ^ Id.to_string field_id
          in
          ptr_to_cell field rest
      in
      let innermost_ptr = ptr_to_cell "(*_write)" br.tmc_cells in
      let type_str = pp_expr inner_ti.tca_type_expr in
      Sexpr
        (CPPbinop
           ( "=",
             CPPvar (Id.of_string "_write"),
             CPPraw
               ( "&std::get<typename " ^ type_str ^ "::"
                 ^ inner_ti.tca_ctor_name ^ ">(" ^ innermost_ptr
                 ^ "->v_mut())." ^ Id.to_string field_id ) ))
    | None ->
      let innermost_name = List.rev cell_names |> List.hd in
      let type_str = pp_expr inner_ti.tca_type_expr in
      let get_expr =
        CPPraw
          ("std::get<typename " ^ type_str ^ "::" ^ inner_ti.tca_ctor_name ^ ">")
      in
      let v_mut =
        CPPmethod_call (CPPvar innermost_name, Id.of_string "v_mut", [])
      in
      Sexpr
        (CPPbinop
           ( "=",
             CPPvar (Id.of_string "_write"),
             CPPunop
               ("&", CPPget (CPPfun_call (get_expr, [v_mut]), field_id)) ))
  in
  (* 5. Shadow variable updates *)
  let shadow_updates =
    make_shadow_updates shadow_params (filter_by_mask varying br.tmc_rec_args)
  in
  cell_decls @ link_stmts @ patch @ [update_write] @ shadow_updates

(** Rewrite return statements inside a TMC visitor lambda body.

    {b Base cases} (no recursive calls): patch the destination with the base
    value and set [_continue = false].

    {b Tail calls}: update shadow variables (same as tail recursion).

    {b TMC branches}: allocate a cell with a hole, patch the destination,
    update [_last], and update shadow variables. *)
let rec rewrite_tmc_lambda_return ~vt_ret check pp_expr ti varying shadow_params =
  function
  | Sreturn (Some (CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas])))
    when count_calls_expr check scrut = 0
         && List.exists
              (fun lambda ->
                match lambda with
                | CPPlambda (_, _, body, _) ->
                  collect_stmts check ~in_visitor:true body <> []
                | _ -> false )
              lambdas ->
    let rw = rewrite_tmc_lambda_return ~vt_ret check pp_expr ti varying shadow_params in
    let new_lambdas =
      map_visit_lambdas ~ret_ty:None
        ~rewrite:(fun _ body -> List.concat_map rw body)
        lambdas
    in
    make_visit_stmt scrut new_lambdas
  | Sreturn (Some e) ->
    ( match check e with
    | Some cs ->
      (* Tail call — just update shadow variables *)
      make_shadow_updates shadow_params (filter_by_mask varying cs.cs_args)
    | None ->
      let n = count_calls_expr check e in
      if n = 0 then
        (* Base case — patch destination and stop.
           For value-type returns, wrap in make_shared. *)
        patch_tmc_dest ~vt_ret:None pp_expr ti (wrap_base_for_vt vt_ret e)
        @ [Sbreak]
      else
        (* TMC branch — allocate cell(s) with holes, patch, continue *)
        match try_tmc_decompose check e with
        | Some br ->
          build_tmc_branch_stmts ~vt_ret pp_expr ti br varying shadow_params
        | None ->
          (* Shouldn't happen if try_tmc_classify was correct, but fallback *)
          [Sreturn (Some e)] )
  | Sif (cond, then_br, else_br) ->
    let rw = rewrite_tmc_lambda_return ~vt_ret check pp_expr ti varying shadow_params in
    rewrite_if_with_reuse_bypass check cond
      (List.concat_map rw then_br)
      (List.concat_map rw else_br)
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    let rw = rewrite_tmc_lambda_return ~vt_ret check pp_expr ti varying shadow_params in
    [
      Scustom_case
        ( ty,
          scrut,
          tyargs,
          List.map
            (fun (ps, ret_ty, body) -> (ps, ret_ty, List.concat_map rw body))
            branches,
          err );
    ]
  | Smatch (branches, default) ->
    let rw = rewrite_tmc_lambda_return ~vt_ret check pp_expr ti varying shadow_params in
    [
      Smatch
        ( List.map
            (fun br ->
              let reuse =
                if count_calls_stmts check br.smb_body > 0 then None
                else br.smb_reuse
              in
              { br with smb_body = List.concat_map rw br.smb_body;
                        smb_reuse = reuse })
            branches,
          Option.map (List.concat_map rw) default );
    ]
  | Sblock stmts ->
    let rw = rewrite_tmc_lambda_return ~vt_ret check pp_expr ti varying shadow_params in
    [Sblock (List.concat_map rw stmts)]
  | s -> [s]

(** Rewrite a top-level statement for TMC.  Handles [std::visit] returns and
    direct returns at the statement level. *)
let rec rewrite_tmc_visit_stmt ~vt_ret check pp_expr ti varying shadow_params = function
  | Sreturn (Some e) ->
    ( match check e with
    | Some cs ->
      (* Direct tail call *)
      let assigns =
        make_shadow_updates shadow_params (filter_by_mask varying cs.cs_args)
      in
      Sblock (assigns @ [Scontinue])
    | None ->
    match e with
    | CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas]) ->
      let new_lambdas =
        map_visit_lambdas ~ret_ty:None
          ~rewrite:(fun _ body ->
            List.concat_map
              (rewrite_tmc_lambda_return ~vt_ret check pp_expr ti varying shadow_params)
              body )
          lambdas
      in
      Sexpr (make_visit_expr scrut new_lambdas)
    | _ ->
      (* Direct base return *)
      let n = count_calls_expr check e in
      if n = 0 then
        Sblock (patch_tmc_dest ~vt_ret:None pp_expr ti (wrap_base_for_vt vt_ret e)
                @ [Sbreak])
      else
        (* TMC branch at top level *)
        match try_tmc_decompose check e with
        | Some br ->
          Sblock (build_tmc_branch_stmts ~vt_ret pp_expr ti br varying shadow_params
                  @ [Scontinue])
        | None -> Sreturn (Some e) )
  | Sif (cond, then_br, else_br) ->
    let rw = rewrite_tmc_visit_stmt ~vt_ret check pp_expr ti varying shadow_params in
    Sif (cond, List.map rw then_br, List.map rw else_br)
  | Sswitch (scrut, r, branches, default) ->
    let rw = rewrite_tmc_visit_stmt ~vt_ret check pp_expr ti varying shadow_params in
    Sswitch
      (scrut, r, List.map (fun (id, body) -> (id, List.map rw body)) branches, default)
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    let rw = rewrite_tmc_visit_stmt ~vt_ret check pp_expr ti varying shadow_params in
    Scustom_case
      ( ty,
        scrut,
        tyargs,
        List.map
          (fun (ps, ret_ty, body) -> (ps, ret_ty, List.map rw body))
          branches,
        err )
  | Smatch (branches, default) ->
    let rw = rewrite_tmc_visit_stmt ~vt_ret check pp_expr ti varying shadow_params in
    Smatch
      ( List.map
          (fun br ->
            (* Strip reuse from TMC branches: the reuse path would bypass
               the TMC loop with a plain recursive call, defeating stack
               safety.  TMC's O(1) stack guarantee trumps reuse's single
               allocation saving. *)
            let reuse =
              if count_calls_stmts check br.smb_body > 0 then None
              else br.smb_reuse
            in
            { br with smb_body = List.map rw br.smb_body;
                      smb_reuse = reuse })
          branches,
        Option.map (List.map rw) default )
  | Sblock stmts ->
    let rw = rewrite_tmc_visit_stmt ~vt_ret check pp_expr ti varying shadow_params in
    Sblock (List.map rw stmts)
  | s -> s

(** Transform a TMC-eligible function body into a [while] loop with
    destination-passing style.

    @param param_inits Optional custom initializers for shadow variables
    @param check Call checker for identifying recursive calls
    @param pp_expr Expression pretty-printer (for rendering types in std::get)
    @param ti TMC info from {!try_tmc_classify}
    @param params Function parameters
    @param ret_ty Return type
    @param body Function body
    @return Transformed body with TMC while loop *)
let transform_tmc ?(param_inits = []) check pp_expr ti params ret_ty body =
  let vt_ret = if is_value_type_ret ret_ty then Some ret_ty else None in
  let varying = find_varying_params check params body in
  let varying_params = filter_by_mask varying params in
  let shadow_params =
    List.map (fun (id, ty) -> (shadow_name id, ty)) varying_params
  in
  let subs =
    List.map2 (fun (id, _) (sid, _) -> (id, sid)) varying_params shadow_params
  in
  (* For value-type returns, _head is unique_ptr<ret_ty> and _write points
     into the unique_ptr chain.  For pointer returns, _head is the bare type. *)
  let head_ty = match vt_ret with
    | Some t -> Tunique_ptr t
    | None -> ret_ty
  in
  let head_decl = Sdecl_init (Id.of_string "_head", head_ty) in
  let write_decl =
    Sasgn (Id.of_string "_write", Some (Tptr head_ty),
           CPPunop ("&", CPPvar (Id.of_string "_head")))
  in
  (* Shadow variable declarations.
     For pointer params with custom inits (e.g., _self = this in methods), only
     strip references but keep const — const T* must stay const to match this.
     For other params (typically const shared_ptr<T>&), strip both ref and const
     so the shadow variable becomes a mutable shared_ptr<T>. *)
  let shadow_decls =
    List.map2
      (fun (orig_id, ty) (shadow_id, _) ->
        let has_custom_init = List.mem_assoc orig_id param_inits in
        let init_expr =
          match List.assoc_opt orig_id param_inits with
          | Some custom -> custom
          | None ->
            if (not has_custom_init) && is_moveable_param_type ty
            then CPPmove (CPPvar orig_id)
            else CPPvar orig_id
        in
        let shadow_ty =
          if has_custom_init then strip_ref_type ty
          else strip_ref_and_const_type ty
        in
        Sasgn (shadow_id, Some shadow_ty, init_expr) )
      varying_params
      shadow_params
  in
  (* Substitute param references in body *)
  let body' = List.map (subst_stmt subs) body in
  (* Rewrite body for TMC, then flatten unnecessary Sblock wrappers *)
  let body'' =
    List.map
      (rewrite_tmc_visit_stmt ~vt_ret check pp_expr ti varying shadow_params)
      body'
    |> strip_unnecessary_blocks
  in
  (* For value-type returns, dereference _head (shared_ptr → value) *)
  let ret_expr = match vt_ret with
    | Some _ -> CPPmove (CPPderef (CPPvar (Id.of_string "_head")))
    | None -> CPPvar (Id.of_string "_head")
  in
  [head_decl; write_decl]
  @ shadow_decls
  @ [
      Swhile (CPPbool true, body'');
      Sreturn (Some ret_expr);
    ]

(** {3 Frame-based non-tail recursion helpers} *)

(** A collected call frame — saved expression info + handler body. *)
type call_frame_info = {
  cf_name : string;
      (** e.g. "_Call1" — assigned when the push statement is generated *)
  cf_saved_types : cpp_type list;
  cf_saved_exprs : cpp_expr list;
      (** for decltype fallback when type is Tunknown *)
  cf_env : (Id.t * cpp_type) list;
      (** type env at frame creation, for decltype resolution *)
  cf_handler : cpp_stmt list;
}

(** Type environment for inferring saved expression types. *)

(** Collect type bindings from a list of statements. Handles
    [Sasgn(id, Some ty, _)] and [Sdecl(id, ty)]. Also recurses into Scustom_case
    branches to pick up pattern-bound variables. *)
let rec collect_type_env (stmts : cpp_stmt list) : (Id.t * cpp_type) list =
  List.concat_map
    (fun s ->
      match s with
      | Sasgn (id, Some ty, _) -> [(id, ty)]
      | Sdecl (id, ty) -> [(id, ty)]
      | Scustom_case (_, _, _, branches, _) ->
        List.concat_map
          (fun (ps, _, body) -> ps @ collect_type_env body)
          branches
      | Sif (_, then_br, else_br) ->
        collect_type_env then_br @ collect_type_env else_br
      | Smatch (branches, default) ->
        List.concat_map
          (fun br ->
            (* Register structured-binding field types so that
               [infer_saved_type] can resolve them for frame structs. *)
            let field_type_bindings =
              List.map
                (fun (bname, ty, _) -> (bname, ty))
                br.smb_field_bindings
            in
            (* Also register the aggregate binding for frame-dispatch
               branches (which use [smb_var] without structured bindings). *)
            let var_binding =
              match br.smb_var with
              | Some id when br.smb_field_bindings = [] ->
                [(id, Tmod (TMconst, br.smb_ctor_type))]
              | _ -> []
            in
            let reuse_env =
              match br.smb_reuse with
              | Some (_, _, stmts) -> collect_type_env stmts
              | None -> []
            in
            field_type_bindings @ var_binding
            @ reuse_env @ collect_type_env br.smb_body )
          branches
        @ (match default with Some ss -> collect_type_env ss | None -> [])
      | Sblock ss -> collect_type_env ss
      | _ -> [] )
    stmts

(** Collect typed bindings from lambda params. *)
let type_env_of_lambda_params (params : (cpp_type * Id.t option) list) :
    (Id.t * cpp_type) list =
  List.filter_map
    (fun (ty, id_opt) ->
      match id_opt with
      | Some id -> Some (id, ty)
      | None -> None )
    params

(** Combine lambda parameter types, body declarations, and outer env
    into a single type environment. *)
let build_lambda_env lparams body env =
  type_env_of_lambda_params lparams @ collect_type_env body @ env

(** Look up a variable's type in the environment. *)
let lookup_var_type env id = List.assoc_opt id env

(** Given template parameters and a type variable id, find the return type of a
    TTfun constraint if the template param is function-typed. *)
let lookup_tparam_return_type tparams id =
  let name = Id.to_string id in
  List.find_map
    (fun (tt, tparam_id) ->
      if String.equal (Id.to_string tparam_id) name then
        match
          tt
        with
        | TTfun (_, cod) -> Some cod
        | _ -> None
      else
        None )
    tparams

(** Extract the underlying type variable id from a forwarding-reference type.
    [Tref(Tref(Tvar(_, Some id)))] → [Some id] *)
let rec extract_fwd_ref_tvar = function
  | Tref inner -> extract_fwd_ref_tvar inner
  | Tvar (_, Some id) -> Some id
  | _ -> None

(** Infer the type of a saved expression from the type environment and template
    params. Falls back to the function's return type. *)
let rec infer_saved_type tparams (env : (Id.t * cpp_type) list) (e : cpp_expr) :
    cpp_type =
  let result =
    match e with
    | CPPvar id ->
      ( match lookup_var_type env id with
      | Some ty -> strip_ref_type ty
      | None -> Tunknown )
    | CPPmove inner -> infer_saved_type tparams env inner
    | CPPderef inner ->
      ( match infer_saved_type tparams env inner with
      | Tshared_ptr t | Tunique_ptr t | Tptr t -> t
      | t -> t )
    | CPPbinop (_, lhs, _) -> infer_saved_type tparams env lhs
    | CPPfun_call (CPPvar f, _) ->
      ( match lookup_var_type env f with
      | Some (Tfun (_, cod)) -> cod
      | Some ty ->
        (* f might be a template param with forwarding ref type *)
        ( match extract_fwd_ref_tvar ty with
        | Some tvar_id ->
          ( match lookup_tparam_return_type tparams tvar_id with
          | Some cod -> cod
          | None -> Tunknown )
        | None -> Tunknown )
      | None -> Tunknown )
    | CPPfun_call (CPPnamespace (_, CPPvar f), _) ->
      ( match lookup_var_type env f with
      | Some (Tfun (_, cod)) -> cod
      | _ -> Tunknown )
    | CPPfun_call (CPPlambda (_, Some ret_ty, _, _), _) -> ret_ty
    | CPPfun_call (CPPglob _, _) -> Tunknown
    | CPPfun_call (CPPmember (inner, id), [])
      when String.equal (Id.to_string id) "get" ->
      (* shared_ptr::get() / unique_ptr::get() returns a raw pointer.
         Infer from the inner expression. *)
      let inner_ty = infer_saved_type tparams env inner in
      ( match inner_ty with
      | Tptr t -> Tptr t  (* already a pointer *)
      | Tshared_ptr t -> Tptr t  (* shared_ptr<T> → T* *)
      | Tunique_ptr t -> Tptr t  (* unique_ptr<T> → T* *)
      | _ -> Tunknown )
    | _ -> Tunknown
  in
  result

(** Collect free variables from an expression.
    Mutually recursive with [free_vars_stmt] and [free_vars_body]. *)
let rec free_vars_expr = function
  | CPPvar id -> [id]
  | CPPfun_call (f, args) ->
    free_vars_expr f @ List.concat_map free_vars_expr args
  | CPPmethod_call (obj, _, args) ->
    free_vars_expr obj @ List.concat_map free_vars_expr args
  | CPPmove e | CPPderef e | CPPforward (_, e) | CPPnamespace (_, e) ->
    free_vars_expr e
  | CPPbinop (_, e1, e2) -> free_vars_expr e1 @ free_vars_expr e2
  | CPPget (e, _)
   |CPPget' (e, _)
   |CPPmember (e, _)
   |CPParrow (e, _)
   |CPPqualified (e, _) -> free_vars_expr e
  | CPPstructmk (_, _, args)
   |CPPstruct (_, _, args)
   |CPPstruct_id (_, _, args)
   |CPPnew (_, args) -> List.concat_map free_vars_expr args
  | CPPshared_ptr_ctor (_, e) | CPPunique_ptr_ctor (_, e) -> free_vars_expr e
  | CPPoverloaded es -> List.concat_map free_vars_expr es
  | CPPlambda (params, _, body, _) ->
    let bound = List.filter_map (fun (_, id_opt) -> id_opt) params in
    let body_fv = free_vars_body body in
    List.filter (fun v -> not (List.exists (Id.equal v) bound)) body_fv
  | _ -> []

(** Collect free variables from a single statement. Statement-level companion
    of {!free_vars_expr}; recurses into branches and sub-expressions. *)
and free_vars_stmt = function
  | Sreturn (Some e) -> free_vars_expr e
  | Sreturn None -> []
  | Sexpr e -> free_vars_expr e
  | Sasgn (_, _, e) -> free_vars_expr e
  | Sderef_asgn (id, e) -> id :: free_vars_expr e
  | Sif (c, t, f) ->
    free_vars_expr c @ free_vars_body t @ free_vars_body f
  | Scustom_case (_, s, _, bs, _) ->
    free_vars_expr s
    @ List.concat_map
        (fun (ps, _, b) ->
          let pat_bound = List.map fst ps in
          let body_fv = free_vars_body b in
          List.filter
            (fun id -> not (List.exists (Id.equal id) pat_bound))
            body_fv )
        bs
  | Sswitch (s, _, bs, _) ->
    free_vars_expr s
    @ List.concat_map (fun (_, b) -> free_vars_body b) bs
  | Smatch (branches, default) ->
    List.concat_map
      (fun br ->
        let fv = free_vars_expr br.smb_scrutinee
          @ List.concat_map free_vars_expr br.smb_extra_conds
          @ ( match br.smb_reuse with
            | Some (cond, _, stmts) ->
              free_vars_expr cond @ free_vars_body stmts
            | None -> [] )
          @ free_vars_body br.smb_body in
        (* Filter out variables bound by this branch: structured-binding
           field names and/or the aggregate binding variable. *)
        let bound_ids =
          List.map (fun (id, _, _) -> id) br.smb_field_bindings
          @ (match br.smb_var with Some id -> [id] | None -> [])
        in
        List.filter
          (fun v -> not (List.exists (Id.equal v) bound_ids))
          fv )
      branches
    @ (match default with Some ss -> free_vars_body ss | None -> [])
  | Sblock ss -> free_vars_body ss
  | _ -> []

(** Collect free variables from a list of statements, properly excluding
    variables defined by [Sasgn] or [Sdecl] bindings in preceding statements.
    Tracks sequential scoping so that a variable defined in statement [i] is
    not considered free when referenced in statement [j > i]. *)
and free_vars_body (stmts : cpp_stmt list) : Id.t list =
  let rec go defined = function
    | [] -> []
    | stmt :: rest ->
      let newly_defined =
        match stmt with
        | Sasgn (id, Some _, _) -> [id]
        | Sdecl (id, _) -> [id]
        | _ -> []
      in
      let stmt_fvs = free_vars_stmt stmt in
      let filtered =
        List.filter
          (fun v -> not (List.exists (Id.equal v) defined))
          stmt_fvs
      in
      filtered @ go (newly_defined @ defined) rest
  in
  go [] stmts

(** Remove duplicate [Id.t] values, preserving first-occurrence order. *)
let dedup_ids ids =
  let seen = Hashtbl.create 8 in
  List.filter
    (fun id ->
      let name = Id.to_string id in
      if Hashtbl.mem seen name then
        false
      else (
        Hashtbl.add seen name ();
        true ) )
    ids

(** Substitute [CPPvar old_id] with [CPPvar new_id] throughout an expression,
    statement, or statement list. Used to eliminate trivial variable aliases
    like [auto _cs = _result;] by replacing [_cs] with [_result] directly. *)
let rec subst_var_expr old_id new_id e =
  let fe e = subst_var_expr old_id new_id e in
  match e with
  | CPPvar id when Id.equal id old_id -> CPPvar new_id
  | _ -> Minicpp.map_expr fe (subst_var_stmt old_id new_id) (fun t -> t) e

and subst_var_stmt old_id new_id s =
  let fe e = subst_var_expr old_id new_id e in
  let fs s = subst_var_stmt old_id new_id s in
  Minicpp.map_stmt fe fs (fun t -> t) s

let subst_var_stmts old_id new_id stmts =
  List.map (subst_var_stmt old_id new_id) stmts

(** Substitute [CPPderef (CPPvar target_id)] with [CPPvar target_id] throughout
    an expression, statement, or statement list.

    When {!Translation.gen_local_fix_shared_ptr} generates a
    shared_ptr fixpoint, all call sites use dereferenced calls
    (i.e. [CPPfun_call(CPPderef(CPPvar f), args)]).  After
    {!loopify_inner_lambdas} converts the recursion into a loop, the
    indirection is no longer needed.  This function strips the [CPPderef]
    wrapper so subsequent code sees plain [CPPvar f] calls and the emitted
    C++ uses direct calls instead of dereferenced ones. *)
let rec un_deref_var_expr target_id e =
  let fe e = un_deref_var_expr target_id e in
  match e with
  | CPPderef (CPPvar id) when Id.equal id target_id -> CPPvar id
  | _ -> Minicpp.map_expr fe (un_deref_var_stmt target_id) (fun t -> t) e

and un_deref_var_stmt target_id s =
  let fe e = un_deref_var_expr target_id e in
  let fs s = un_deref_var_stmt target_id s in
  Minicpp.map_stmt fe fs (fun t -> t) s

let un_deref_var_stmts target_id stmts =
  List.map (un_deref_var_stmt target_id) stmts

(** Collect free variables from Scustom_case branch bodies, excluding
    pattern-bound variables. Deduplicated.

    Branch format: [(params, ret_ty, body)] where [params] is
    [(Id.t * cpp_type) list] — the pattern-bound variables with their types. *)
let collect_branch_free_vars branches =
  List.concat_map
    (fun (params, _ret_ty2, body) ->
      let pat_bound = List.map fst params in
      let all_vars = List.concat_map free_vars_stmt body in
      List.filter (fun id -> not (List.exists (Id.equal id) pat_bound)) all_vars )
    branches
  |> dedup_ids

(** Collect free variables from visit (pattern-match) lambda bodies, excluding
    lambda-bound parameters. The result is deduplicated.

    Each lambda in [lambdas] is a [CPPlambda] whose parameters bind pattern
    variables. This function extracts the free variables of each body, filters
    out those bound by the lambda parameters, and returns a single deduplicated
    list. Used when lowering visit expressions that contain recursive calls in
    their lambda branches (visit-with-scrutinee-call handling).

    @param lambdas List of CPP expressions, typically [CPPlambda] nodes from a
                   [CPPoverloaded] visit
    @return Deduplicated list of [Id.t] free variables across all lambda bodies *)
let collect_visit_free_vars lambdas =
  List.concat_map
    (fun lambda ->
      match lambda with
      | CPPlambda (lparams, _, body, _) ->
        let pat_bound = List.filter_map (fun (_, id_opt) -> id_opt) lparams in
        let body_fvs = free_vars_body body in
        List.filter
          (fun id -> not (List.exists (Id.equal id) pat_bound))
          body_fvs
      | _ -> [] )
    lambdas
  |> dedup_ids

(** Rewrite a Scustom_case branch's returns to assign to _result instead. *)
let rec rewrite_returns_to_result = function
  | Sreturn (Some e) -> assign_result e
  | Sif (c, t, f) ->
    [
      Sif
        ( c,
          List.concat_map rewrite_returns_to_result t,
          List.concat_map rewrite_returns_to_result f );
    ]
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    [
      Scustom_case
        ( ty,
          scrut,
          tyargs,
          List.map
            (fun (ps, ret_ty2, body) ->
              (ps, ret_ty2, List.concat_map rewrite_returns_to_result body) )
            branches,
          err );
    ]
  | Sswitch (scrut, ty, branches, default) ->
    [
      Sswitch
        ( scrut,
          ty,
          List.map
            (fun (lbl, body) ->
              (lbl, List.concat_map rewrite_returns_to_result body) )
            branches,
          default );
    ]
  | Smatch (branches, default) ->
    [
      Smatch
        ( List.map
            (fun br ->
              { br with smb_body = List.concat_map rewrite_returns_to_result br.smb_body })
            branches,
          Option.map (List.concat_map rewrite_returns_to_result) default );
    ]
  | Sblock ss -> [Sblock (List.concat_map rewrite_returns_to_result ss)]
  | s -> [s]

(** {3 Continuation variable helpers}

    When a recursive call occurs mid-statement-sequence (e.g., [let x = f(n) in
    rest]), the "rest" statements form a continuation. Variables that are free in
    [rest] but defined before it must be saved in the call frame and restored in
    the handler. These helpers factor out the repeated pattern of computing,
    filtering, binding, and registering continuation variables. *)

(** Compute the free variables of a continuation (the "rest" of a statement
    sequence). Excludes variables that are defined within [rest] itself and
    the special [_result] accumulator.

    @param rest The remaining statements (the continuation)
    @return Sorted, unique list of free variable [Id.t] values *)
let compute_rest_free_vars rest =
  let rest_defined =
    List.filter_map
      (function Sasgn (vid, _, _) -> Some vid | _ -> None)
      rest
  in
  List.concat_map free_vars_stmt rest
  |> List.filter (fun v -> not (List.exists (Id.equal v) rest_defined))
  |> List.sort_uniq (fun a b -> Id.compare a b)

(** Filter continuation free variables, removing the assigned variable and
    the [_result] accumulator.

    @param exclude_id The variable being assigned (not needed in continuation)
    @param rest_free The free variables of the continuation
    @return Filtered list of continuation variables *)
let filter_cont_vars ~exclude_id rest_free =
  List.filter
    (fun fv ->
      (not (Id.equal fv exclude_id))
      && not (Id.equal fv (Id.of_string "_result")))
    rest_free

(** Generate statements that bind continuation variables from frame fields.
    Produces [<type> <name> = _f._s<offset+i>;] for each continuation variable.

    @param offset Starting field index in the frame
    @param cont_vars The continuation variable names
    @param cont_types Their types (parallel to [cont_vars])
    @param pp_type Type printer function
    @return List of raw C++ binding statements *)
let make_cont_bindings ~offset cont_vars cont_types =
  List.mapi
    (fun i id ->
      let ty = List.nth cont_types i in
      let ty_opt = if ty = Tunknown then None else Some ty in
      let field_expr =
        CPPmember (CPPvar (Id.of_string "_f"),
                   Id.of_string ("_s" ^ string_of_int (offset + i)))
      in
      let rhs = match ty with Tunique_ptr _ -> CPPmove field_expr | _ -> field_expr in
      Sasgn (id, ty_opt, rhs))
    cont_vars

(** Build a type environment from continuation variables and their types,
    prepended to an existing environment.

    @param cont_vars Continuation variable names
    @param cont_types Their types (parallel to [cont_vars])
    @param env The existing type environment
    @return Extended type environment *)
let make_cont_env cont_vars cont_types env =
  List.map2 (fun id ty -> (id, ty)) cont_vars cont_types @ env

(** Register a call frame in the mutable [frames_ref] accumulator.

    @param frames_ref Mutable reference to the list of collected frames
    @param name Frame struct name (e.g., ["_Call1"])
    @param saved_types Types of saved expressions
    @param saved_exprs The saved expressions (for decltype fallback)
    @param env Type environment at frame creation point
    @param handler The handler body statements *)
let register_frame frames_ref ~name ~saved_types ~saved_exprs ~env ~handler =
  frames_ref :=
    !frames_ref
    @ [{cf_name = name; cf_saved_types = saved_types;
        cf_saved_exprs = saved_exprs; cf_env = env; cf_handler = handler}]

(** {3 Frame-based non-tail rewrite}

    Rewrite the body for the Enter handler, replacing recursive returns with
    frame pushes. Collects [call_frame_info] for each call site so that the
    caller can generate the corresponding handler lambdas.

    The [call_counter] ref assigns sequential IDs (starting from 1). The
    [frames_ref] accumulates call frame info in order. *)

(** Build a stack push expression. Uses [CPPfun_call(CPPmember(...))] so that
    [CPPvar "_stack"] is visible to capture detection (ensuring [[&]] capture),
    and renders with [.] not [->]. *)
let make_stack_push arg =
  Sexpr
    (CPPfun_call
       ( CPPmember (CPPvar (Id.of_string "_stack"), Id.of_string "emplace_back"),
         [arg] ) )

(** Read the [i]-th saved field from frame variable [_f]. Generates [_f._sI]. *)
let frame_field i =
  CPPmember (CPPvar (Id.of_string "_f"), Id.of_string ("_s" ^ string_of_int i))

(** Read [n] consecutive saved fields from frame [_f], starting at [offset].
    Returns a list of expressions [[_f._s{offset}; ...; _f._s{offset+n-1}]]. *)
let frame_fields ?(offset = 0) n =
  List.init n (fun i -> frame_field (offset + i))


(** Clone a unique_ptr expression for saving in a frame struct.
    [unique_ptr<T>] is move-only, but the source may be a const reference
    from a borrowed pattern match.  We clone the value and wrap in
    [make_unique] to produce a new owned [unique_ptr<T>].
    Non-unique_ptr expressions pass through unchanged. *)
let clone_for_frame ty expr =
  match ty with
  | Tunique_ptr inner ->
    CPPfun_call (CPPmk_unique inner,
                 [CPPmethod_call (expr, Id.of_string "clone", [])])
  | _ -> expr

(** Apply [clone_for_frame] to parallel type and expression lists. *)
let clone_for_frame_list types exprs =
  List.map2 clone_for_frame types exprs

(** {4 Frame construction helpers}

    These helpers reduce code duplication when constructing frame instances and
    managing the frame counter. *)

(** Generate a unique frame name by incrementing the counter. Returns ["_Call{id}"]
    where {i id} is the counter's value before incrementing.

    @param counter A mutable reference to the frame counter (starts at 0, incremented
                   each time a frame is created)
    @return A string like ["_Call0"], ["_Call1"], etc. *)
let make_call_frame_name (counter : int ref) : string =
  let id = !counter in
  counter := id + 1;
  "_Call" ^ string_of_int id

(** Construct an [_Enter] frame expression with the given arguments.

    Generates [_Enter\{arg1, arg2, ...\}] as a [CPPstruct_id] expression.

    @param args The arguments to save in the Enter frame (typically function parameters)
    @return A [CPPstruct_id] expression representing the frame instance *)
let make_enter_frame (args : cpp_expr list) : cpp_expr =
  CPPstruct_id (Id.of_string "_Enter", [], args)


(** Batch-infer types for a list of saved expressions.

    @param tparams Template parameters context
    @param env Type environment for variable lookups
    @param exprs The expressions whose types to infer
    @return A list of inferred [cpp_type] values, parallel to [exprs] *)
let infer_saved_types tparams env exprs =
  List.map (infer_saved_type tparams env) exprs

(** Build a decompose_single_call handler body: reads saved values from [_f._sN]
    and _result, reconstructs the expression. *)
let build_decompose_handler (d : decomposed) n_saved =
  let saved_vars = frame_fields n_saved in
  let result_var = CPPvar (Id.of_string "_result") in
  let rebuilt = d.d_rebuild saved_vars result_var in
  assign_result rebuilt

(** Build a Scustom_case scrutinee handler body: reads saved variables from
    frame, then dispatches on _result. [rewrite_body] is a function to rewrite
    return statements in the branch bodies (may handle recursive calls via frame
    pushes). *)
let build_scrutinee_handler
    ~rewrite_body
    ~saved_types
    unique_vars
    ty
    tyargs
    branches
    err =
  let n = List.length unique_vars in
  (* Bind saved vars from frame fields *)
  let bindings =
    List.mapi
      (fun i id ->
        let ty = List.nth saved_types i in
        let ty_opt = if ty = Tunknown then None else Some ty in
        let field_expr =
          CPPmember (CPPvar (Id.of_string "_f"),
                     Id.of_string ("_s" ^ string_of_int i))
        in
        (* Move unique_ptr fields out of the owned frame *)
        let rhs = match ty with
          | Tunique_ptr _ -> CPPmove field_expr
          | _ -> field_expr
        in
        Sasgn (id, ty_opt, rhs))
      unique_vars
  in
  (* Rewrite branch bodies *)
  let rewritten_branches =
    List.map
      (fun (ps, ret_ty2, body) ->
        (ps, ret_ty2, List.concat_map rewrite_body body) )
      branches
  in
  let case_stmt =
    Scustom_case
      (ty, CPPvar (Id.of_string "_result"), tyargs, rewritten_branches, err)
  in
  if n > 0 then
    bindings @ [case_stmt]
  else
    [case_stmt]

(** Search through an argument list for an element matching [search_fn].

    Iterates left-to-right through [args] applying [search_fn] to each element.
    On the first match, returns [Some (result, rebuild)] where [result] is the
    value produced by [search_fn] and [rebuild] is a function that reconstructs
    the full argument list with a replacement element at the matched position.
    Returns [None] if no element matches.

    This enables "find and replace in context" patterns: locate a subexpression
    within a function's arguments, transform it, and rebuild the outer call.

    @param search_fn Predicate/extractor applied to each argument
    @param args      The argument list to search
    @return [Some (result, rebuild)] on match, [None] otherwise. [rebuild] takes
            a replacement expression and returns the full argument list with that
            element substituted at the matched position. *)
let search_in_args search_fn args =
  let rec try_args rev_pre = function
    | [] -> None
    | arg :: post ->
    match search_fn arg with
    | Some result -> Some (result, fun x -> List.rev rev_pre @ [x] @ post)
    | None -> try_args (arg :: rev_pre) post
  in
  try_args [] args

(** Find a visit subexpression with recursive calls inside a larger expression.
    Returns [Some (scrut, lambdas, rebuild)] where [rebuild result] reconstructs
    the original expression with the visit replaced by [result]. Returns [None]
    if no such visit is found. *)
let rec find_inner_visit check = function
  | CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas])
    when count_calls_expr check scrut = 0
         && List.exists
              (fun lambda ->
                match lambda with
                | CPPlambda (_, _, body, _) ->
                  collect_stmts check ~in_visitor:true body <> []
                | _ -> false )
              lambdas -> Some (scrut, lambdas, Fun.id)
  | CPPfun_call (f, args) ->
    ( match search_in_args (find_inner_visit check) args with
    | Some ((scrut, lambdas, rebuild), mk_args) ->
      Some (scrut, lambdas, fun x -> CPPfun_call (f, mk_args (rebuild x)))
    | None -> None )
  | CPPmove e ->
    ( match find_inner_visit check e with
    | Some (scrut, lambdas, rebuild) ->
      Some (scrut, lambdas, fun x -> CPPmove (rebuild x))
    | None -> None )
  | _ -> None

(** Find an immediately-invoked lambda expression (IIFE) containing recursive
    calls. Returns [(body, ret_ty, rebuild)] where [rebuild] wraps a result
    expression back into the surrounding context. *)
let rec find_inner_iife check = function
  | CPPfun_call (CPPlambda ([], ret_ty, body, _cap), [])
    when collect_stmts check ~in_visitor:false body <> [] ->
    Some (body, ret_ty, Fun.id)
  | CPPfun_call (f, args) ->
    ( match search_in_args (find_inner_iife check) args with
    | Some ((body, ret_ty, rebuild), mk_args) ->
      Some (body, ret_ty, fun x -> CPPfun_call (f, mk_args (rebuild x)))
    | None -> None )
  | CPPmove e ->
    ( match find_inner_iife check e with
    | Some (body, ret_ty, rebuild) ->
      Some (body, ret_ty, fun x -> CPPmove (rebuild x))
    | None -> None )
  | CPPstruct_id (name, tys, args) ->
    ( match search_in_args (find_inner_iife check) args with
    | Some ((body, ret_ty, rebuild), mk_args) ->
      Some (body, ret_ty, fun x -> CPPstruct_id (name, tys, mk_args (rebuild x)))
    | None -> None )
  | CPPstructmk (name, tys, args) ->
    ( match search_in_args (find_inner_iife check) args with
    | Some ((body, ret_ty, rebuild), mk_args) ->
      Some (body, ret_ty, fun x -> CPPstructmk (name, tys, mk_args (rebuild x)))
    | None -> None )
  | _ -> None

(** {3 N-call decomposition}

    Decompose an expression into ALL of its recursive calls. Returns the list of
    argument lists (one per call, in left-to-right order), any non-recursive
    expressions that need saving, and a combine function that reconstructs the
    final expression from saved expressions and call results. *)

type all_calls_decomp = {
  acd_calls : cpp_expr list list;
  acd_saved : cpp_expr list;
  acd_combine : cpp_expr list -> cpp_expr list -> cpp_expr;
}

(** Decompose an expression into all N recursive calls.  Generalizes
    {!decompose_double_call} to arbitrary counts.

    {b Example.}  For [a + f(x) * f(y)]:
    - [acd_saved = [a]] — non-recursive sub-expressions that must be computed
      before the loop and stored in the stack frame.
    - [acd_calls = [[x]; [y]]] — argument lists for each recursive call, in
      left-to-right order.
    - [acd_combine saved results] — rebuilds the original expression:
      [saved.(0) + results.(0) * results.(1)].

    The combine callback receives saved values and call results as lists
    (in the same order as [acd_saved] and [acd_calls]) and produces the
    final expression.  This is used by the enter-frame rewriter to emit
    stack frames that save intermediate values across recursive calls. *)
let rec decompose_all_calls check expr =
  match check expr with
  | Some cs ->
    Some
      {
        acd_calls = [cs.cs_args];
        acd_saved = [];
        acd_combine = (fun _saved results -> List.hd results);
      }
  | None ->
  match expr with
  | CPPbinop (op, e1, e2) ->
    let c1 = count_calls_expr check e1 in
    let c2 = count_calls_expr check e2 in
    if c1 >= 1 && c2 >= 1 then
      match
        (decompose_all_calls check e1, decompose_all_calls check e2)
      with
      | Some d1, Some d2 ->
        let n1_calls = List.length d1.acd_calls in
        let n1_saved = List.length d1.acd_saved in
        Some
          {
            acd_calls = d1.acd_calls @ d2.acd_calls;
            acd_saved = d1.acd_saved @ d2.acd_saved;
            acd_combine =
              (fun saved results ->
                let saved1 = List.filteri (fun i _ -> i < n1_saved) saved in
                let saved2 = List.filteri (fun i _ -> i >= n1_saved) saved in
                let results1 = List.filteri (fun i _ -> i < n1_calls) results in
                let results2 =
                  List.filteri (fun i _ -> i >= n1_calls) results
                in
                CPPbinop
                  ( op,
                    d1.acd_combine saved1 results1,
                    d2.acd_combine saved2 results2 ) );
          }
      | _ -> None
    else if c1 >= 1 && c2 = 0 then
      match
        decompose_all_calls check e1
      with
      | Some d1 ->
        let n1_saved = List.length d1.acd_saved in
        Some
          {
            d1 with
            acd_saved = d1.acd_saved @ [e2];
            acd_combine =
              (fun saved results ->
                let saved1 = List.filteri (fun i _ -> i < n1_saved) saved in
                let e2' = List.nth saved n1_saved in
                CPPbinop (op, d1.acd_combine saved1 results, e2') );
          }
      | None -> None
    else if c1 = 0 && c2 >= 1 then
      match
        decompose_all_calls check e2
      with
      | Some d2 ->
        Some
          {
            acd_saved = e1 :: d2.acd_saved;
            acd_calls = d2.acd_calls;
            acd_combine =
              (fun saved results ->
                let e1' = List.hd saved in
                let saved2 = List.tl saved in
                CPPbinop (op, e1', d2.acd_combine saved2 results) );
          }
      | None -> None
    else
      None
  | CPPfun_call (f, args) when count_calls_expr check f = 0 ->
    let n_args = List.length args in
    let arg_calls = List.mapi (fun i a -> (i, count_calls_expr check a)) args in
    let rec_indices = List.filter (fun (_, c) -> c > 0) arg_calls in
    let non_rec_indices =
      List.filter (fun (_, c) -> c = 0) arg_calls |> List.map fst
    in
    let non_rec_args = List.map (fun i -> List.nth args i) non_rec_indices in
    let rec_decomps =
      List.map
        (fun (i, _) -> (i, decompose_all_calls check (List.nth args i)))
        rec_indices
    in
    if List.for_all (fun (_, d) -> d <> None) rec_decomps then
      let decomps = List.map (fun (i, d) -> (i, Option.get d)) rec_decomps in
      let all_calls = List.concat_map (fun (_, d) -> d.acd_calls) decomps in
      let all_saved_from_decomps =
        List.concat_map (fun (_, d) -> d.acd_saved) decomps
      in
      let all_saved = all_saved_from_decomps @ non_rec_args in
      let combine saved results =
        let n_decomp_saved = List.length all_saved_from_decomps in
        let decomp_saved = List.filteri (fun i _ -> i < n_decomp_saved) saved in
        let outer_saved = List.filteri (fun i _ -> i >= n_decomp_saved) saved in
        let _, _, rebuilt_args =
          List.fold_left
            (fun (saved_off, result_off, rebuilt) (i, d) ->
              let n_s = List.length d.acd_saved in
              let n_r = List.length d.acd_calls in
              let d_saved =
                List.filteri
                  (fun j _ -> j >= saved_off && j < saved_off + n_s)
                  decomp_saved
              in
              let d_results =
                List.filteri
                  (fun j _ -> j >= result_off && j < result_off + n_r)
                  results
              in
              let rebuilt_expr = d.acd_combine d_saved d_results in
              (saved_off + n_s, result_off + n_r, rebuilt @ [(i, rebuilt_expr)]) )
            (0, 0, [])
            decomps
        in
        let new_args =
          List.init n_args (fun i ->
            match List.assoc_opt i rebuilt_args with
            | Some e -> e
            | None ->
              let pos =
                List.length (List.filter (fun j -> j < i) non_rec_indices)
              in
              List.nth outer_saved pos )
        in
        CPPfun_call (f, new_args)
      in
      Some {acd_calls = all_calls; acd_saved = all_saved; acd_combine = combine}
    else
      None
  | CPPmove inner ->
    ( match decompose_all_calls check inner with
    | Some d ->
      Some
        {
          d with
          acd_combine =
            (fun saved results -> CPPmove (d.acd_combine saved results));
        }
    | None -> None )
  | _ -> None

(** Generate chained [_CallN] frames for an N-call decomposition within the
    nontail frame-based transformation.

    When a single expression contains N >= 2 recursive calls (e.g.,
    [f(a) + f(b) + f(c)]), each call must be sequentialized into separate stack
    frames. This function creates a chain of N [_CallN] frames:

    - Frames 0..N-2 (intermediate): Each saves partial results from earlier
      calls plus the arguments for remaining calls. Its handler pushes the next
      [_CallN+1] frame (with accumulated partials) and an [_Enter] frame for the
      next recursive call.

    - Frame N-1 (final): Saves all N-1 partial results plus any non-recursive
      saved expressions. Its handler combines all partial results with the last
      [_result] using [acd.acd_combine] to produce the final value.

    The function also emits the initial push statements: push the first [_Call]
    frame (saving remaining call arguments and non-recursive expressions), then
    push [_Enter] for the first recursive call.

    @param check               Recursive call checker
    @param varying             Bitmask indicating which parameters vary across calls
    @param tparams             Type parameters of the function
    @param env                 Type environment for inferring saved expression types
    @param ret_ty              Return type of the function (used for partial result types)
    @param pp_type             Type pretty-printer
    @param call_counter        Mutable counter for generating unique frame names
    @param frames_ref          Mutable list where generated {!call_frame_info} are appended
    @param varying_param_types Types of the varying parameters
    @param acd                 The {!all_calls_decomp} describing all recursive calls,
                               saved expressions, and the combine function
    @return List of statements that push the first [_CallN] frame and the
            first [_Enter] frame onto the stack *)
let gen_chained_call_frames
    check
    varying
    tparams
    env
    ret_ty
    pp_type
    call_counter
    frames_ref
    varying_param_types
    (acd : all_calls_decomp) =
  let n_calls = List.length acd.acd_calls in
  let n_saved = List.length acd.acd_saved in
  let saved_types = infer_saved_types tparams env acd.acd_saved in
  let saved_exprs_conv = clone_for_frame_list saved_types acd.acd_saved in
  let rec gen_frames call_idx =
    if call_idx = n_calls - 1 then (
      let call_name = make_call_frame_name call_counter in
      let n_partials = call_idx in
      let partial_types = List.init n_partials (fun _ -> ret_ty) in
      let all_saved_types = partial_types @ saved_types in
      let all_saved_exprs =
        List.init n_partials (fun _ -> CPPvar (Id.of_string "_result"))
        @ saved_exprs_conv
      in
      let handler =
        let partials = frame_fields n_partials in
        let saved_vars = frame_fields ~offset:n_partials n_saved in
        let all_results = partials @ [CPPvar (Id.of_string "_result")] in
        let combined = acd.acd_combine saved_vars all_results in
        assign_result combined
      in
      register_frame frames_ref ~name:call_name ~saved_exprs:all_saved_exprs
        ~saved_types:all_saved_types ~env ~handler;
      call_name )
    else
      let call_name = make_call_frame_name call_counter in
      let next_name = gen_frames (call_idx + 1) in
      let n_partials = call_idx in
      let partial_types = List.init n_partials (fun _ -> ret_ty) in
      let remaining_calls =
        List.filteri (fun i _ -> i > call_idx) acd.acd_calls
      in
      let remaining_args =
        List.concat_map
          (fun args -> filter_by_mask varying args)
          remaining_calls
      in
      (* Use varying param types for remaining call args — more reliable than
         infer_saved_type which can't handle CPPfun_call(CPPglob ...) *)
      let n_remaining_calls = List.length remaining_calls in
      let remaining_arg_types =
        List.concat (List.init n_remaining_calls (fun _ -> varying_param_types))
      in
      (* Clone unique_ptr args for frame storage *)
      let remaining_args_conv =
        clone_for_frame_list remaining_arg_types remaining_args in
      let all_saved_types = partial_types @ remaining_arg_types @ saved_types in
      let all_saved_exprs =
        List.init n_partials (fun _ -> CPPvar (Id.of_string "_result"))
        @ remaining_args_conv
        @ saved_exprs_conv
      in
      let handler =
        let n_remaining_args_for_next =
          List.length
            (filter_by_mask varying (List.nth acd.acd_calls (call_idx + 1)))
        in
        let next_args =
          frame_fields ~offset:n_partials n_remaining_args_for_next
        in
        let n_remaining_total = List.length remaining_args in
        let next_partials = frame_fields n_partials in
        let after_next_args =
          frame_fields
            ~offset:(n_partials + n_remaining_args_for_next)
            (n_remaining_total - n_remaining_args_for_next)
        in
        let saved_from_f =
          frame_fields ~offset:(n_partials + n_remaining_total) n_saved
        in
        let next_push_args =
          next_partials
          @ [CPPvar (Id.of_string "_result")]
          @ after_next_args
          @ saved_from_f
        in
        [
          make_stack_push
            (CPPstruct_id (Id.of_string next_name, [], next_push_args));
          make_stack_push (CPPstruct_id (Id.of_string "_Enter", [], next_args));
        ]
      in
      register_frame frames_ref ~name:call_name
        ~saved_types:all_saved_types ~saved_exprs:all_saved_exprs ~env
        ~handler;
      call_name
  in
  let first_call_name = gen_frames 0 in
  let first_args = filter_by_mask varying (List.hd acd.acd_calls) in
  let remaining_calls = List.tl acd.acd_calls in
  let remaining_args =
    List.concat_map (fun args -> filter_by_mask varying args) remaining_calls
  in
  (* Clone unique_ptr args for frame storage *)
  let remaining_arg_types_init =
    let n = List.length remaining_calls in
    List.concat (List.init n (fun _ -> varying_param_types))
  in
  let remaining_args_conv =
    clone_for_frame_list remaining_arg_types_init remaining_args in
  let first_frame_saved = remaining_args_conv @ saved_exprs_conv in
  [
    make_stack_push
      (CPPstruct_id (Id.of_string first_call_name, [], first_frame_saved));
    make_stack_push (CPPstruct_id (Id.of_string "_Enter", [], first_args));
  ]

(** Lift recursive calls out of an expression into temporary variable
    assignments. Each recursive call [f(args)] is replaced by a fresh variable
    [_condN] and a corresponding [Sasgn(_condN, Some ret_ty, f(args))] is
    prepended before the rewritten statement.

    Returns [(new_expr, lifted_stmts, lifted_env)] where:
    - [new_expr] has all recursive calls replaced by variables
    - [lifted_stmts] are the [Sasgn] declarations to prepend
    - [lifted_env] extends [env] with the new variable bindings *)
let lift_recursive_calls check ret_ty env expr =
  let bindings = ref [] in
  let counter = ref 0 in
  let rec replace e =
    match check e with
    | Some _cs ->
      let name = "_cond" ^ string_of_int !counter in
      counter := !counter + 1;
      let cid = Id.of_string name in
      bindings := !bindings @ [(cid, e)];
      CPPvar cid
    | None -> map_expr replace Fun.id Fun.id e
  in
  let new_expr = replace expr in
  let lifted_stmts =
    List.map (fun (cid, orig_e) -> Sasgn (cid, Some ret_ty, orig_e)) !bindings
  in
  let lifted_env = List.map (fun (cid, _) -> (cid, ret_ty)) !bindings @ env in
  (new_expr, lifted_stmts, lifted_env)

(** Rewrite a single return statement for the [_Enter] handler in frame-based
    non-tail recursion transformation.

    This function is the core of the frame-based rewriting strategy. It analyzes
    return statements and rewrites them into stack pushes when they contain
    recursive calls. The rewriting depends on the number and structure of recursive
    calls:

    - {b 0 calls}: Assign directly to [_result]
    - {b 1 call}: Decompose via {!decompose_single_call}, push [_Call] + [_Enter]
    - {b 2 calls}: Decompose via {!decompose_double_call}, push chained frames
    - {b N calls}: Decompose via {!decompose_all_calls}, push N frames

    Special cases handled:
    - [std::visit] with recursive scrutinee (decompose scrutinee first)
    - IIFEs ([CPPfun_call(CPPlambda(...))] containing recursive calls
    - Nested recursive calls (e.g., [f(x, f(y, z))])
    - Recursive calls in saved frame expressions

    @param check The call checker for identifying recursive calls
    @param varying Boolean mask indicating which parameters vary across recursive calls
    @param tparams Template parameter context for type inference
    @param env Type environment mapping variables to types
    @param ret_ty The return type of the function being loopified
    @param pp_type Type pretty-printer for generating type strings
    @param call_counter Mutable counter for generating unique [_CallN] frame names
    @param frames_ref Mutable list collecting [call_frame_info] records for all Call frames
    @param varying_param_types Types of varying parameters (for reliable type inference)
    @param stmt The statement to rewrite (typically a [Sreturn] statement)
    @return A list of rewritten statements (frame pushes or result assignments) *)
let rec rewrite_enter_lambda_return
    check
    varying
    tparams
    env
    ret_ty
    pp_type
    (call_counter : int ref)
    (frames_ref : call_frame_info list ref)
    varying_param_types = function
  | Sreturn (Some (CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas])))
    when count_calls_expr check scrut >= 1 ->
    (* Visit with recursive call in scrutinee, and possibly recursive branches.
       Decompose scrutinee, create Call frame, handler does visit on _result.
       Lambda bodies are rewritten with rewrite_enter_stmts to handle both
       recursive and non-recursive branches. *)
    ( match decompose_single_call check scrut with
    | Some d ->
      let call_name = make_call_frame_name call_counter in
      let lambda_fvs = collect_visit_free_vars lambdas in
      let lambda_saved = List.map (fun id -> CPPvar id) lambda_fvs in
      let lambda_types = infer_saved_types tparams env lambda_saved in
      let all_saved = d.d_saved @ lambda_saved in
      let all_types = infer_saved_types tparams env d.d_saved @ lambda_types in
      let n_d = List.length d.d_saved in
      let handler =
        let rebuild_vars = frame_fields n_d in
        let rebuilt_scrut =
          d.d_rebuild rebuild_vars (CPPvar (Id.of_string "_result"))
        in
        let bindings =
          List.mapi
            (fun i id ->
              let ty = List.nth lambda_types i in
              let ty_opt = if ty = Tunknown then None else Some ty in
              Sasgn (id, ty_opt,
                     CPPmember (CPPvar (Id.of_string "_f"),
                                Id.of_string ("_s" ^ string_of_int (n_d + i)))))
            lambda_fvs
        in
        let new_lambdas =
          map_visit_lambdas ~ret_ty:(Some Tvoid)
            ~rewrite:(fun lparams body ->
              let lenv = build_lambda_env lparams body env in
              rewrite_enter_stmts check varying tparams lenv ret_ty pp_type
                call_counter frames_ref varying_param_types body)
            lambdas
        in
        bindings @ [Sexpr (make_visit_expr rebuilt_scrut new_lambdas)]
      in
      register_frame frames_ref ~name:call_name ~saved_types:all_types
        ~saved_exprs:all_saved ~env ~handler;
      let all_saved_conv = clone_for_frame_list all_types all_saved in
      [
        make_stack_push (CPPstruct_id (Id.of_string call_name, [], all_saved_conv));
        make_stack_push
          (CPPstruct_id
             (Id.of_string "_Enter", [], filter_by_mask varying d.d_rec_args) );
      ]
    | None ->
      (* Cannot decompose scrutinee — execute inline *)
      assign_result (make_visit_expr scrut lambdas) )
  | Sreturn (Some (CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas])))
    when count_calls_expr check scrut = 0
         && List.exists
              (fun lambda ->
                match lambda with
                | CPPlambda (_, _, body, _) ->
                  collect_stmts check ~in_visitor:true body <> []
                | _ -> false )
              lambdas ->
    (* Lower nested visit — recurse into each lambda body *)
    let new_lambdas =
      map_visit_lambdas ~ret_ty:(Some Tvoid)
        ~rewrite:(fun lparams body ->
          let lenv = build_lambda_env lparams body env in
          rewrite_enter_stmts check varying tparams lenv ret_ty pp_type
            call_counter frames_ref varying_param_types body)
        lambdas
    in
    make_visit_stmt scrut new_lambdas
  | Sreturn (Some e) ->
    let n_calls = count_calls_expr check e in
    if n_calls = 0 then
      (* count_calls_expr doesn't count inside lambdas — check for visits with
         recursive calls in their lambda bodies *)
        match
          find_inner_visit check e
        with
      | Some (scrut, lambdas, rebuild) ->
        (* Push the continuation (rebuild) into each visit branch: each branch's
           return value gets wrapped in rebuild(...) *)
        let new_lambdas =
          List.map
            (fun lambda ->
              match lambda with
              | CPPlambda (lparams, _lret_ty, body, _capture) ->
                let extended_body =
                  List.map
                    (fun stmt ->
                      match stmt with
                      | Sreturn (Some result) -> Sreturn (Some (rebuild result))
                      | s -> s )
                    body
                in
                let lenv = build_lambda_env lparams extended_body env in
                let new_body =
                  rewrite_enter_stmts
                    check
                    varying
                    tparams
                    lenv
                    ret_ty
                    pp_type
                    call_counter
                    frames_ref
                    varying_param_types
                    extended_body
                in
                CPPlambda (lparams, Some Tvoid, new_body, false)
              | e -> e )
            lambdas
        in
        make_visit_stmt scrut new_lambdas
      | None ->
      (* Check for IIFE containing recursive calls *)
      match find_inner_iife check e with
      | Some (iife_body, _iife_ret_ty, rebuild) ->
        (* Wrap each return in the IIFE body with the surrounding rebuild *)
        let extended_body =
          List.map
            (fun stmt ->
              match stmt with
              | Sreturn (Some result) -> Sreturn (Some (rebuild result))
              | s -> s )
            iife_body
        in
        let lenv = collect_type_env extended_body @ env in
        let new_body =
          rewrite_enter_stmts
            check
            varying
            tparams
            lenv
            ret_ty
            pp_type
            call_counter
            frames_ref
            varying_param_types
            extended_body
        in
        new_body
      | None ->
        (* True base case — no recursive calls anywhere *)
        assign_result e
    else if n_calls = 1 then
      match
        decompose_single_call check e
      with
      | Some d ->
        (* Check if any saved expression contains a recursive call *)
        let saved_with_calls =
          List.mapi (fun i s -> (i, s, check s)) d.d_saved
        in
        let recursive_saved =
          List.filter (fun (_, _, cs_opt) -> cs_opt <> None) saved_with_calls
        in
        ( match recursive_saved with
        | (idx, rec_saved_expr, Some rec_cs) :: _ ->
          (* One of the saved expressions is a recursive call — decompose it
             first *)
          let final_call_name = make_call_frame_name call_counter in
          let n_saved = List.length d.d_saved in
          let saved_types = infer_saved_types tparams env d.d_saved in
          let final_handler = build_decompose_handler d n_saved in
          register_frame frames_ref ~name:final_call_name ~saved_types
            ~saved_exprs:d.d_saved ~env ~handler:final_handler;
          (* Create intermediate Call frame that will push the final Call frame
             after getting _result *)
          let other_saved = List.filteri (fun i _ -> i <> idx) d.d_saved in
          let inter_call_name = make_call_frame_name call_counter in
          let inter_saved_types =
            infer_saved_types tparams env other_saved
          in
          let n_other = List.length other_saved in
          let inter_handler =
            let other_vars = frame_fields n_other in
            let final_saved =
              List.mapi
                (fun i _ ->
                  if i = idx then
                    CPPvar (Id.of_string "_result")
                  else if i < idx then
                    List.nth other_vars i
                  else
                    List.nth other_vars (i - 1) )
                d.d_saved
            in
            let push_final =
              make_stack_push
                (CPPstruct_id (Id.of_string final_call_name, [], final_saved))
            in
            let push_enter =
              make_stack_push
                (CPPstruct_id
                   ( Id.of_string "_Enter",
                     [],
                     filter_by_mask varying d.d_rec_args ) )
            in
            [push_final; push_enter]
          in
          register_frame frames_ref ~name:inter_call_name
            ~saved_types:inter_saved_types ~saved_exprs:other_saved ~env
            ~handler:inter_handler;
          [
            make_stack_push
              (CPPstruct_id (Id.of_string inter_call_name, [], other_saved));
            make_stack_push
              (CPPstruct_id
                 ( Id.of_string "_Enter",
                   [],
                   filter_by_mask varying rec_cs.cs_args ) );
          ]
        | [] ->
          (* No recursive calls in saved expressions — original path *)
          let call_name = make_call_frame_name call_counter in
          let n_saved = List.length d.d_saved in
          let saved_types = infer_saved_types tparams env d.d_saved in
          let handler = build_decompose_handler d n_saved in
          let saved_exprs_conv = clone_for_frame_list saved_types d.d_saved in
          register_frame frames_ref ~name:call_name ~saved_types
            ~saved_exprs:saved_exprs_conv ~env ~handler;
          let push_call =
            make_stack_push
              (CPPstruct_id (Id.of_string call_name, [], saved_exprs_conv))
          in
          let push_enter =
            make_stack_push
              (CPPstruct_id
                 (Id.of_string "_Enter", [], filter_by_mask varying d.d_rec_args)
              )
          in
          [push_call; push_enter]
        | _ ->
          assert false (* cannot happen: only one recursive call in the list *)
        )
      | None ->
      match check e with
      | Some cs ->
        (* Check if any argument contains a nested recursive call *)
        let nested_indices =
          List.mapi (fun i a -> (i, count_calls_expr check a)) cs.cs_args
          |> List.filter (fun (_, c) -> c > 0)
        in
        if nested_indices = [] then (* Simple tail call — just push Enter *)
          [
            make_stack_push
              (CPPstruct_id
                 (Id.of_string "_Enter", [], filter_by_mask varying cs.cs_args)
              );
          ]
        else (
          (* Nested call: e.g. f(m', f(m, n')) — compute inner call first, then
             push Enter for outer call with result *)
            match
              nested_indices
            with
          | [(idx, 1)] ->
            let rec_arg = List.nth cs.cs_args idx in
            let non_rec_info =
              List.mapi (fun i a -> (i, a)) cs.cs_args
              |> List.filter (fun (i, _) -> i <> idx)
            in
            let non_rec_args = List.map snd non_rec_info in
            let call_name = make_call_frame_name call_counter in
            let saved_types =
              infer_saved_types tparams env non_rec_args
            in
            let n_saved = List.length non_rec_args in
            let handler =
              let saved_vars = frame_fields n_saved in
              let outer_args =
                List.init (List.length cs.cs_args) (fun i ->
                  if i = idx then
                    CPPvar (Id.of_string "_result")
                  else
                    let pos =
                      List.length
                        (List.filter (fun (j, _) -> j < i) non_rec_info)
                    in
                    List.nth saved_vars pos )
              in
              [
                make_stack_push
                  (CPPstruct_id
                     ( Id.of_string "_Enter",
                       [],
                       filter_by_mask varying outer_args ) );
              ]
            in
            register_frame frames_ref ~name:call_name ~saved_types
              ~saved_exprs:non_rec_args ~env ~handler;
            ( match check rec_arg with
            | Some inner_cs ->
              [
                make_stack_push
                  (CPPstruct_id (Id.of_string call_name, [], non_rec_args));
                make_stack_push
                  (CPPstruct_id
                     ( Id.of_string "_Enter",
                       [],
                       filter_by_mask varying inner_cs.cs_args ) );
              ]
            | None ->
            match decompose_single_call check rec_arg with
            | Some d ->
              let inner_call_name = make_call_frame_name call_counter in
              let inner_saved_types =
                infer_saved_types tparams env d.d_saved
              in
              let inner_n = List.length d.d_saved in
              let inner_handler =
                let inner_saved_vars = frame_fields inner_n in
                let rebuilt =
                  d.d_rebuild inner_saved_vars (CPPvar (Id.of_string "_result"))
                in
                [
                  Sexpr
                    (CPPbinop ("=", CPPvar (Id.of_string "_result"), rebuilt));
                ]
              in
              register_frame frames_ref ~name:inner_call_name
                ~saved_types:inner_saved_types ~saved_exprs:d.d_saved ~env
                ~handler:inner_handler;
              [
                make_stack_push
                  (CPPstruct_id (Id.of_string call_name, [], non_rec_args));
                make_stack_push
                  (CPPstruct_id (Id.of_string inner_call_name, [], d.d_saved));
                make_stack_push
                  (CPPstruct_id
                     ( Id.of_string "_Enter",
                       [],
                       filter_by_mask varying d.d_rec_args ) );
              ]
            | None ->
              (* Cannot decompose — execute inline *)
              assign_result e )
          | _ ->
            (* Multiple nested calls or complex pattern — execute inline *)
            assign_result e )
      | None ->
        (* Unhandled — execute inline *)
        assign_result e
    else (
      (* Multiple recursive calls — try double decomposition *)
        match
          decompose_double_call check e
        with
      | Some dd ->
        (* Chained _Call frames: 1. Push _Call1{second_args, dd_saved} +
           _Enter{first_args} 2. _Call1 handler: save _result as left, push
           _Call2{left, dd_saved} + _Enter{second_args} 3. _Call2 handler:
           _result = combine(dd_saved_vars, left, _result) *)
        let call1_name = make_call_frame_name call_counter in
        let call2_name = make_call_frame_name call_counter in
        let n_dd_saved = List.length dd.dd_saved in
        (* _Call2 saves: left_result (ret_ty) + dd_saved *)
        let call2_saved_exprs =
          CPPvar (Id.of_string "_result") :: dd.dd_saved
        in
        let call2_saved_types =
          ret_ty :: infer_saved_types tparams env dd.dd_saved
        in
        let call2_handler =
          let left = frame_field 0 in
          let saved_vars =
            List.init n_dd_saved (fun i -> frame_field (i + 1))
          in
          let combined =
            dd.dd_combine saved_vars left (CPPvar (Id.of_string "_result"))
          in
          assign_result combined
        in
        register_frame frames_ref ~name:call2_name
          ~saved_types:call2_saved_types ~saved_exprs:call2_saved_exprs ~env
          ~handler:call2_handler;
        (* _Call1 saves: second_args (varying-filtered) + dd_saved *)
        let second_varying = filter_by_mask varying dd.dd_second_args in
        let call1_saved_exprs = second_varying @ dd.dd_saved in
        let call1_saved_types =
          infer_saved_types tparams env call1_saved_exprs
        in
        let n_second = List.length second_varying in
        let call1_handler =
          let second_args = frame_fields n_second in
          let dd_saved_from_f = frame_fields ~offset:n_second n_dd_saved in
          let call2_push_args =
            CPPvar (Id.of_string "_result") :: dd_saved_from_f
          in
          [
            make_stack_push
              (CPPstruct_id (Id.of_string call2_name, [], call2_push_args));
            make_stack_push
              (CPPstruct_id (Id.of_string "_Enter", [], second_args));
          ]
        in
        register_frame frames_ref ~name:call1_name
          ~saved_types:call1_saved_types ~saved_exprs:call1_saved_exprs ~env
          ~handler:call1_handler;
        [
          make_stack_push
            (CPPstruct_id (Id.of_string call1_name, [], call1_saved_exprs));
          make_stack_push
            (CPPstruct_id
               ( Id.of_string "_Enter",
                 [],
                 filter_by_mask varying dd.dd_first_args ) );
        ]
      | None ->
      (* Double decomposition failed — try N-call decomposition *)
      match decompose_all_calls check e with
      | Some acd
        when List.length acd.acd_calls >= 2
             && not (has_higher_order_template_param tparams) ->
        gen_chained_call_frames
          check
          varying
          tparams
          env
          ret_ty
          pp_type
          call_counter
          frames_ref
          varying_param_types
          acd
      | _ ->
        (* Cannot decompose — execute inline *)
        assign_result e )
  | Sif (cond, then_br, else_br) when count_calls_expr check cond >= 1 ->
    (* Recursive calls in condition — lift them into assignments before the
       if *)
    let new_cond, lifted_stmts, lifted_env =
      lift_recursive_calls check ret_ty env cond
    in
    let all_stmts = lifted_stmts @ [Sif (new_cond, then_br, else_br)] in
    rewrite_enter_stmts
      check
      varying
      tparams
      lifted_env
      ret_ty
      pp_type
      call_counter
      frames_ref
      varying_param_types
      all_stmts
  | Sif (cond, then_br, else_br) ->
    let rw_stmts =
      rewrite_enter_stmts
        check
        varying
        tparams
        env
        ret_ty
        pp_type
        call_counter
        frames_ref
        varying_param_types
    in
    let rw_then = rw_stmts then_br in
    let rw_else = rw_stmts else_br in
    rewrite_if_with_reuse_bypass check cond rw_then rw_else
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    ( match check scrut with
    | Some cs ->
      let call_name = make_call_frame_name call_counter in
      let unique_vars = collect_branch_free_vars branches in
      let saved_exprs = List.map (fun id -> CPPvar id) unique_vars in
      let saved_types = infer_saved_types tparams env saved_exprs in
      let rw_handler =
        rewrite_enter_lambda_return
          check
          varying
          tparams
          env
          ret_ty
          pp_type
          call_counter
          frames_ref
          varying_param_types
      in
      let handler =
        build_scrutinee_handler
          ~rewrite_body:rw_handler
          ~saved_types
          unique_vars
          ty
          tyargs
          branches
          err
      in
      (* Clone unique_ptr-typed variables for frame storage *)
      let saved_exprs_conv = clone_for_frame_list saved_types saved_exprs in
      register_frame frames_ref ~name:call_name ~saved_types
        ~saved_exprs:saved_exprs_conv ~env ~handler;
      let push_call =
        make_stack_push (CPPstruct_id (Id.of_string call_name, [], saved_exprs_conv))
      in
      let push_enter =
        make_stack_push
          (CPPstruct_id
             (Id.of_string "_Enter", [], filter_by_mask varying cs.cs_args) )
      in
      [push_call; push_enter]
    | None when count_calls_expr check scrut >= 1 ->
      (* Recursive calls in scrutinee (not a direct call) — lift into
         assignments *)
      let new_scrut, lifted_stmts, lifted_env =
        lift_recursive_calls check ret_ty env scrut
      in
      let all_stmts =
        lifted_stmts @ [Scustom_case (ty, new_scrut, tyargs, branches, err)]
      in
      rewrite_enter_stmts
        check
        varying
        tparams
        lifted_env
        ret_ty
        pp_type
        call_counter
        frames_ref
        varying_param_types
        all_stmts
    | None ->
      [
        Scustom_case
          ( ty,
            scrut,
            tyargs,
            List.map
              (fun (ps, ret_ty2, body) ->
                let lenv = collect_type_env body @ env in
                ( ps,
                  ret_ty2,
                  rewrite_enter_stmts
                    check
                    varying
                    tparams
                    lenv
                    ret_ty
                    pp_type
                    call_counter
                    frames_ref
                    varying_param_types
                    body ) )
              branches,
            err );
      ] )
  | Smatch (branches, default) ->
    (* Augment the env with each branch's binding variable types so that
       [infer_saved_types] resolves field types correctly per-branch. *)
    let rw_branch br =
      let branch_env =
        (* Register structured-binding field types. *)
        let fb_env =
          List.map (fun (bname, ty, _) -> (bname, ty)) br.smb_field_bindings
        in
        (* Also register aggregate binding for frame-dispatch branches. *)
        let var_env =
          match br.smb_var with
          | Some id when br.smb_field_bindings = [] ->
            [(id, Tmod (TMconst, br.smb_ctor_type))]
          | _ -> []
        in
        fb_env @ var_env @ env
      in
      let rw = rewrite_enter_stmts check varying tparams branch_env ret_ty
            pp_type call_counter frames_ref varying_param_types in
      (* Strip reuse from branches with recursive calls: the reuse path
         would bypass the loopification with plain recursive calls,
         defeating the stack-safety guarantee. *)
      let reuse =
        if count_calls_stmts check br.smb_body > 0 then None
        else br.smb_reuse
      in
      { br with smb_reuse = reuse; smb_body = rw br.smb_body }
    in
    let rw_default =
      rewrite_enter_stmts check varying tparams env ret_ty pp_type
        call_counter frames_ref varying_param_types
    in
    [Smatch (List.map rw_branch branches, Option.map rw_default default)]
  | Sblock stmts ->
    let rw_stmts =
      rewrite_enter_stmts
        check
        varying
        tparams
        env
        ret_ty
        pp_type
        call_counter
        frames_ref
        varying_param_types
    in
    [Sblock (rw_stmts stmts)]
  | Sasgn (id, ty_opt, e) when count_calls_expr check e >= 1 ->
    (* Let-bound recursive call: create a Call frame with empty continuation.
       The caller (rewrite_enter_stmts) will handle the full continuation. *)
    let n_calls = count_calls_expr check e in
    if n_calls = 1 then
      match
        check e
      with
      | Some cs ->
        (* Direct call: id = f(args) *)
        let call_name = make_call_frame_name call_counter in
        let handler = [Sasgn (id, ty_opt, CPPvar (Id.of_string "_result"))] in
        register_frame frames_ref ~name:call_name ~saved_types:[]
          ~saved_exprs:[] ~env ~handler;
        let push_call =
          make_stack_push (CPPstruct_id (Id.of_string call_name, [], []))
        in
        let push_enter =
          make_stack_push
            (CPPstruct_id
               (Id.of_string "_Enter", [], filter_by_mask varying cs.cs_args) )
        in
        [push_call; push_enter]
      | None ->
      match decompose_single_call check e with
      | Some d ->
        let call_name = make_call_frame_name call_counter in
        let n_saved = List.length d.d_saved in
        let saved_types = infer_saved_types tparams env d.d_saved in
        let handler =
          let result_bindings = frame_fields n_saved in
          let rebuilt =
            d.d_rebuild result_bindings (CPPvar (Id.of_string "_result"))
          in
          [Sasgn (id, ty_opt, rebuilt)]
        in
        register_frame frames_ref ~name:call_name ~saved_types
          ~saved_exprs:d.d_saved ~env ~handler;
        let saved_exprs_conv = clone_for_frame_list saved_types d.d_saved in
        let push_call =
          make_stack_push (CPPstruct_id (Id.of_string call_name, [], saved_exprs_conv))
        in
        let push_enter =
          make_stack_push
            (CPPstruct_id
               (Id.of_string "_Enter", [], filter_by_mask varying d.d_rec_args)
            )
        in
        [push_call; push_enter]
      | None ->
        (* Cannot decompose — execute inline *)
        [Sasgn (id, ty_opt, e)]
    else (
      (* Multiple recursive calls in Sasgn — try double decomposition *)
        match
          decompose_double_call check e
        with
      | Some dd ->
        let call1_name = make_call_frame_name call_counter in
        let call2_name = make_call_frame_name call_counter in
        let n_dd_saved = List.length dd.dd_saved in
        (* _Call2: combine left and right results *)
        let call2_saved_exprs =
          CPPvar (Id.of_string "_result") :: dd.dd_saved
        in
        let call2_saved_types =
          ret_ty :: infer_saved_types tparams env dd.dd_saved
        in
        let call2_handler =
          let left = frame_field 0 in
          let saved_vars =
            List.init n_dd_saved (fun i -> frame_field (i + 1))
          in
          let combined =
            dd.dd_combine saved_vars left (CPPvar (Id.of_string "_result"))
          in
          [Sasgn (id, ty_opt, combined)]
        in
        register_frame frames_ref ~name:call2_name
          ~saved_types:call2_saved_types ~saved_exprs:call2_saved_exprs ~env
          ~handler:call2_handler;
        (* _Call1: save left result, push second call *)
        let second_varying = filter_by_mask varying dd.dd_second_args in
        let call1_saved_exprs = second_varying @ dd.dd_saved in
        let call1_saved_types =
          infer_saved_types tparams env call1_saved_exprs
        in
        let n_second = List.length second_varying in
        let call1_handler =
          let second_args = frame_fields n_second in
          let dd_saved_from_f = frame_fields ~offset:n_second n_dd_saved in
          let call2_push_args =
            CPPvar (Id.of_string "_result") :: dd_saved_from_f
          in
          [
            make_stack_push
              (CPPstruct_id (Id.of_string call2_name, [], call2_push_args));
            make_stack_push
              (CPPstruct_id (Id.of_string "_Enter", [], second_args));
          ]
        in
        register_frame frames_ref ~name:call1_name
          ~saved_types:call1_saved_types ~saved_exprs:call1_saved_exprs ~env
          ~handler:call1_handler;
        [
          make_stack_push
            (CPPstruct_id (Id.of_string call1_name, [], call1_saved_exprs));
          make_stack_push
            (CPPstruct_id
               ( Id.of_string "_Enter",
                 [],
                 filter_by_mask varying dd.dd_first_args ) );
        ]
      | None ->
      (* Double decomposition failed — try N-call decomposition *)
      match decompose_all_calls check e with
      | Some acd when List.length acd.acd_calls >= 2 ->
        let stmts =
          gen_chained_call_frames
            check
            varying
            tparams
            env
            ret_ty
            pp_type
            call_counter
            frames_ref
            varying_param_types
            acd
        in
        (* Patch last frame to assign to id instead of _result *)
        let frames = !frames_ref in
        let last_idx = List.length frames - 1 in
        let last_frame = List.nth frames last_idx in
        let other_frames = List.filteri (fun i _ -> i < last_idx) frames in
        let n_partials = List.length acd.acd_calls - 1 in
        let n_saved = List.length acd.acd_saved in
        let patched_handler =
          let partials = frame_fields n_partials in
          let saved_vars = frame_fields ~offset:n_partials n_saved in
          let all_results = partials @ [CPPvar (Id.of_string "_result")] in
          let combined = acd.acd_combine saved_vars all_results in
          [Sasgn (id, ty_opt, combined)]
        in
        frames_ref :=
          other_frames @ [{last_frame with cf_handler = patched_handler}];
        stmts
      | _ ->
        (* Cannot decompose — execute inline *)
        [Sasgn (id, ty_opt, e)] )
  | Sswitch (scrut, r, branches, default) ->
    let rw_stmts =
      rewrite_enter_stmts
        check
        varying
        tparams
        env
        ret_ty
        pp_type
        call_counter
        frames_ref
        varying_param_types
    in
    let rw_branches =
      List.map
        (fun (id, body) ->
          let lenv = collect_type_env body @ env in
          ( id,
            rewrite_enter_stmts
              check
              varying
              tparams
              lenv
              ret_ty
              pp_type
              call_counter
              frames_ref
              varying_param_types
              body ) )
        branches
    in
    let rw_default = Option.map rw_stmts default in
    [Sswitch (scrut, r, rw_branches, rw_default)]
  | s -> [s]

(** Process a sequence of statements using continuation-passing to handle
    recursive calls in assignment positions.

    This is the core of the nontail frame-based transformation for statement
    sequences. When it encounters [Sasgn(id, ty, e)] where [e] contains one or
    more recursive calls, it captures the remaining statements ([rest]) as a
    "continuation" that is embedded in the Call frame's handler.

    {b Stack frame chaining strategy.}  For [let x = f(a) in rest]:
    + Push [_CallN\{saved_fields\}] — saves continuation variables live across
      the call.
    + Push [_Enter\{args\}] — provides the recursive call's arguments.
    + The loop pops [_Enter], executes the call, stores the result in
      [_result], then pops [_CallN] whose handler binds [x = _result],
      restores saved fields, and processes [rest].

    For nested calls like [let x = f(a) in let y = f(b) in rest], frames
    chain: [_Call1]'s handler processes the [let y = ...] assignment, which
    pushes [_Call2] + [_Enter] for the second call.  The final handler in
    [_Call2] processes [rest].

    The function handles several cases:
    - {b Single direct call}: [let x = f(args) in rest] -- creates one Call
      frame whose handler assigns [_result] to [x] then processes [rest].
    - {b Single decomposed call}: [let x = g(saved, f(args)) in rest] --
      decomposes [e] to extract saved expressions and the recursive call,
      creates a Call frame that reconstructs the expression from frame fields.
    - {b Double call}: [let x = f(a) + f(b) in rest] -- creates two Call
      frames (_Call1 and _Call2) chained together, with the continuation
      embedded in the final _Call2 handler.
    - {b N-call}: [let x = f(a) + f(b) + f(c) in rest] -- delegates to
      {!gen_chained_call_frames} for arbitrary numbers of calls, then patches
      the final frame to include the continuation.
    - {b Non-assignment statements}: delegates to {!rewrite_enter_lambda_return}.

    Continuation variables (free in [rest] but defined before it) are saved in
    each Call frame and restored via [make_cont_bindings] in the handler.

    @param check               Recursive call checker
    @param varying             Bitmask for which parameters vary
    @param tparams             Type parameters
    @param env                 Type environment
    @param ret_ty              Function return type
    @param pp_type             Type pretty-printer
    @param call_counter        Mutable counter for unique frame names
    @param frames_ref          Mutable list where generated frames accumulate
    @param varying_param_types Types of varying parameters
    @param stmts               The statement sequence to process
    @return Rewritten statement list (typically stack push operations) *)
and rewrite_enter_stmts
    check
    varying
    tparams
    env
    ret_ty
    pp_type
    call_counter
    frames_ref
    varying_param_types
    stmts =
  match stmts with
  | [] -> []
  | Sasgn (id, ty_opt, e) :: rest when count_calls_expr check e >= 1 ->
    let n_calls = count_calls_expr check e in
    let rest_free = compute_rest_free_vars rest in
    (* Helper: build continuation handler and register the call frame.
       [~offset] is the field offset where continuation vars start in the
       frame. [assign_expr] is the expression to assign to [id].
       [saved/types] are the frame's saved values (decomposed + continuation).
       [enter_args] are the arguments for the _Enter push. *)
    let make_cont_handler ~offset ~assign_expr ~saved ~types ~enter_args =
      let cont_vars = filter_cont_vars ~exclude_id:id rest_free in
      let cont_saved = List.map (fun cid -> CPPvar cid) cont_vars in
      let cont_types = infer_saved_types tparams env cont_saved in
      let call_name = make_call_frame_name call_counter in
      let bindings = make_cont_bindings ~offset cont_vars cont_types in
      let rest_env = make_cont_env cont_vars cont_types env in
      let rest_processed =
        rewrite_enter_stmts check varying tparams rest_env ret_ty pp_type
          call_counter frames_ref varying_param_types rest
      in
      let handler =
        match assign_expr with
        | CPPvar v when String.length (Id.to_string id) >= 3
            && String.sub (Id.to_string id) 0 3 = "_cs" ->
          (* assign_expr is a plain variable (e.g. _result) and id is a
             scrutinee cache variable (_cs, _cs1, ...) — skip the
             redundant alias [auto _cs = v;] and substitute v for id. *)
          bindings @ subst_var_stmts id v rest_processed
        | _ ->
          bindings @ [Sasgn (id, ty_opt, assign_expr)] @ rest_processed
      in
      let all_saved = saved @ cont_saved in
      let all_types = types @ cont_types in
      let all_saved_conv = clone_for_frame_list all_types all_saved in
      register_frame frames_ref ~name:call_name ~saved_types:all_types
        ~saved_exprs:all_saved_conv ~env ~handler;
      [
        make_stack_push (CPPstruct_id (Id.of_string call_name, [], all_saved_conv));
        make_stack_push (make_enter_frame enter_args);
      ]
    in
    if n_calls = 1 then
      match check e with
      | Some cs ->
        (* Direct call: id = f(args) — no decomposition needed *)
        make_cont_handler
          ~offset:0
          ~assign_expr:(CPPvar (Id.of_string "_result"))
          ~saved:[] ~types:[]
          ~enter_args:(filter_by_mask varying cs.cs_args)
      | None ->
      match decompose_single_call check e with
      | Some d ->
        (* Decomposed call: id = rebuild(saved, f(rec_args)) *)
        let n_d = List.length d.d_saved in
        let d_types = infer_saved_types tparams env d.d_saved in
        let rebuilt =
          d.d_rebuild (frame_fields n_d) (CPPvar (Id.of_string "_result"))
        in
        make_cont_handler
          ~offset:n_d
          ~assign_expr:rebuilt
          ~saved:d.d_saved ~types:d_types
          ~enter_args:(filter_by_mask varying d.d_rec_args)
      | None ->
        [Sasgn (id, ty_opt, e)]
        @ rewrite_enter_stmts check varying tparams env ret_ty pp_type
            call_counter frames_ref varying_param_types rest
    else (
      (* Multiple recursive calls in Sasgn *)
        match decompose_double_call check e with
      | Some dd ->
        let cont_vars = filter_cont_vars ~exclude_id:id rest_free in
        let cont_saved = List.map (fun cid -> CPPvar cid) cont_vars in
        let cont_types = infer_saved_types tparams env cont_saved in
        let n_cont = List.length cont_vars in
        let n_dd_saved = List.length dd.dd_saved in
        let call2_name = make_call_frame_name call_counter in
        let call1_name = make_call_frame_name call_counter in
        (* _Call2: combine left and right results, then process continuation *)
        let call2_saved_exprs =
          (CPPvar (Id.of_string "_result") :: dd.dd_saved) @ cont_saved
        in
        let call2_saved_types =
          (ret_ty :: infer_saved_types tparams env dd.dd_saved)
          @ cont_types
        in
        let call2_handler =
          let left = frame_field 0 in
          let saved_vars = frame_fields ~offset:1 n_dd_saved in
          let combined =
            dd.dd_combine saved_vars left (CPPvar (Id.of_string "_result"))
          in
          let bindings =
            make_cont_bindings ~offset:(1 + n_dd_saved)
              cont_vars cont_types
          in
          let rest_env = make_cont_env cont_vars cont_types env in
          let rest_processed =
            rewrite_enter_stmts check varying tparams rest_env ret_ty pp_type
              call_counter frames_ref varying_param_types rest
          in
          bindings @ [Sasgn (id, ty_opt, combined)] @ rest_processed
        in
        register_frame frames_ref ~name:call2_name
          ~saved_types:call2_saved_types ~saved_exprs:call2_saved_exprs
          ~env ~handler:call2_handler;
        (* _Call1: save left result, push second call *)
        let second_varying = filter_by_mask varying dd.dd_second_args in
        let call1_saved_exprs = second_varying @ dd.dd_saved @ cont_saved in
        let call1_saved_types =
          infer_saved_types tparams env (second_varying @ dd.dd_saved)
          @ cont_types
        in
        let call1_saved_exprs_conv =
          clone_for_frame_list call1_saved_types call1_saved_exprs
        in
        let n_second = List.length second_varying in
        let call1_handler =
          let second_args = frame_fields n_second in
          let dd_saved_from_f = frame_fields ~offset:n_second n_dd_saved in
          let cont_from_f =
            frame_fields ~offset:(n_second + n_dd_saved) n_cont
          in
          let call2_push_args =
            (CPPvar (Id.of_string "_result") :: dd_saved_from_f) @ cont_from_f
          in
          [
            make_stack_push
              (CPPstruct_id (Id.of_string call2_name, [], call2_push_args));
            make_stack_push (make_enter_frame second_args);
          ]
        in
        register_frame frames_ref ~name:call1_name
          ~saved_types:call1_saved_types ~saved_exprs:call1_saved_exprs_conv
          ~env ~handler:call1_handler;
        [
          make_stack_push
            (CPPstruct_id (Id.of_string call1_name, [], call1_saved_exprs_conv));
          make_stack_push
            (make_enter_frame (filter_by_mask varying dd.dd_first_args));
        ]
      | None ->
      (* Double decomposition failed — try N-call decomposition *)
      match decompose_all_calls check e with
      | Some acd when List.length acd.acd_calls >= 2 ->
        let cont_vars = filter_cont_vars ~exclude_id:id rest_free in
        let cont_saved = List.map (fun cid -> CPPvar cid) cont_vars in
        let cont_types = infer_saved_types tparams env cont_saved in
        let n_orig_calls = List.length acd.acd_calls in
        let n_orig_saved = List.length acd.acd_saved in
        let extended_acd = {acd with acd_saved = acd.acd_saved @ cont_saved} in
        let _ =
          gen_chained_call_frames check varying tparams env ret_ty pp_type
            call_counter frames_ref varying_param_types extended_acd
        in
        (* Patch the last generated frame to include assignment +
           continuation *)
        let frames = !frames_ref in
        let last_frame = List.nth frames (List.length frames - 1) in
        let other_frames =
          List.filteri (fun i _ -> i < List.length frames - 1) frames
        in
        let n_partials = n_orig_calls - 1 in
        let bindings =
          make_cont_bindings ~offset:(n_partials + n_orig_saved)
            cont_vars cont_types
        in
        let rest_env = make_cont_env cont_vars cont_types env in
        let rest_processed =
          rewrite_enter_stmts check varying tparams rest_env ret_ty pp_type
            call_counter
            frames_ref
            varying_param_types
            rest
        in
        (* Replace the last handler: instead of assigning _result, assign to id
           and process rest *)
        let patched_handler =
          let partials = frame_fields n_partials in
          let saved_vars = frame_fields ~offset:n_partials n_orig_saved in
          let all_results = partials @ [CPPvar (Id.of_string "_result")] in
          let combined = acd.acd_combine saved_vars all_results in
          bindings @ [Sasgn (id, ty_opt, combined)] @ rest_processed
        in
        let patched_last =
          { last_frame with
            cf_saved_types = last_frame.cf_saved_types @ cont_types;
            cf_saved_exprs = last_frame.cf_saved_exprs @ cont_saved;
            cf_handler = patched_handler }
        in
        frames_ref := other_frames @ [patched_last];
        (* Return the push statements for the first frame *)
        let first_args = filter_by_mask varying (List.hd acd.acd_calls) in
        let remaining_args =
          List.concat_map
            (fun args -> filter_by_mask varying args)
            (List.tl acd.acd_calls)
        in
        let first_frame_saved = remaining_args @ acd.acd_saved @ cont_saved in
        let first_frame_name =
          (List.nth frames (List.length frames - 2)).cf_name
        in
        [
          make_stack_push
            (CPPstruct_id (Id.of_string first_frame_name, [], first_frame_saved));
          make_stack_push (make_enter_frame first_args);
        ]
      | _ ->
        [Sasgn (id, ty_opt, e)]
        @ rewrite_enter_stmts check varying tparams env ret_ty pp_type
            call_counter frames_ref varying_param_types rest )
  | stmt :: rest ->
    rewrite_enter_lambda_return check varying tparams env ret_ty pp_type
      call_counter frames_ref varying_param_types stmt
    @ rewrite_enter_stmts check varying tparams env ret_ty pp_type
        call_counter frames_ref varying_param_types rest

(** Rewrite a single non-tail recursive statement for the Enter handler.

    Thin wrapper around {!rewrite_enter_lambda_return} that collapses a
    multi-statement result into a single [Sblock]. This is the entry point used
    by {!transform_nontail} when rewriting each top-level body statement for the
    Enter handler of the frame-based loop.

    @param check               Recursive call checker
    @param varying             Bitmask for which parameters vary
    @param tparams             Type parameters
    @param env                 Type environment
    @param ret_ty              Function return type
    @param pp_type             Type pretty-printer
    @param call_counter        Mutable counter for unique frame names
    @param frames_ref          Mutable list where generated frames accumulate
    @param varying_param_types Types of varying parameters
    @param stmt                The single statement to rewrite
    @return A single statement (possibly [Sblock] wrapping multiple results) *)
let rewrite_enter_stmt
    check
    varying
    tparams
    env
    ret_ty
    pp_type
    (call_counter : int ref)
    (frames_ref : call_frame_info list ref)
    varying_param_types
    stmt =
  let stmts =
    rewrite_enter_lambda_return
      check
      varying
      tparams
      env
      ret_ty
      pp_type
      call_counter
      frames_ref
      varying_param_types
      stmt
  in
  match stmts with
  | [s] -> s
  | ss -> Sblock ss

(** {2 Multi-recursive (frame-based) transformation}

    For functions with 2 recursive calls per expression (e.g., fib, pascal), we
    use a frame-based stack with Enter/After/Combine variants.

    The stack holds frames representing work to do:
    - [_Enter\{params\}]: compute the function for these parameters
    - [_After\{second_args\}]: first call done, now compute second call
    - [_Combine\{left_result\}]: both calls done, combine results

    A while loop pops frames and dispatches via std::visit. *)

(** Rewrite the body for the Enter handler of a multi-recursive function.
    - Returns with 0 calls → [_result = val;]
    - Returns with 1 call → decompose single, push [_Combine] + [_Enter]
    - Returns with 2 calls → decompose double, push [_After] + [_Enter]
    - Direct tail calls → push [_Enter\{args\}] *)
let rec rewrite_multi_enter check varying = function
  | Sreturn (Some (CPPfun_call (CPPvisit, [scrut; CPPoverloaded lambdas])))
    when count_calls_expr check scrut = 0
         && List.exists
              (fun lambda ->
                match lambda with
                | CPPlambda (_, _, body, _) ->
                  collect_stmts check ~in_visitor:true body <> []
                | _ -> false )
              lambdas ->
    (* Lower nested visit — recurse into each lambda body *)
    let new_lambdas =
      map_visit_lambdas ~ret_ty:(Some Tvoid)
        ~rewrite:(fun _ body ->
          List.concat_map (rewrite_multi_enter check varying) body)
        lambdas
    in
    make_visit_stmt scrut new_lambdas
  | Sreturn (Some e) ->
    let n_calls = count_calls_expr check e in
    if n_calls = 0 then
      (* Check for visits with recursive calls in their lambda bodies *)
        match
          find_inner_visit check e
        with
      | Some (scrut, lambdas, rebuild) ->
        let new_lambdas =
          List.map
            (fun lambda ->
              match lambda with
              | CPPlambda (lparams, _lret_ty, body, _capture) ->
                let extended_body =
                  List.map
                    (fun stmt ->
                      match stmt with
                      | Sreturn (Some result) -> Sreturn (Some (rebuild result))
                      | s -> s )
                    body
                in
                CPPlambda
                  ( lparams,
                    Some Tvoid,
                    List.concat_map
                      (rewrite_multi_enter check varying)
                      extended_body,
                    false )
              | e -> e )
            lambdas
        in
        make_visit_stmt scrut new_lambdas
      | None ->
      match find_inner_iife check e with
      | Some (iife_body, _iife_ret_ty, rebuild) ->
        let extended_body =
          List.map
            (fun stmt ->
              match stmt with
              | Sreturn (Some result) -> Sreturn (Some (rebuild result))
              | s -> s )
            iife_body
        in
        List.concat_map (rewrite_multi_enter check varying) extended_body
      | None ->
        (* True base case *)
        [Sasgn (Id.of_string "_result", None, e)]
    else if n_calls >= 2 then
      (* Double recursive call *)
        match
          decompose_double_call check e
        with
      | Some dd ->
        let push_after =
          make_stack_push
            (CPPstruct_id
               ( Id.of_string "_After",
                 [],
                 filter_by_mask varying dd.dd_second_args ))
        in
        let push_enter =
          make_stack_push
            (CPPstruct_id
               ( Id.of_string "_Enter",
                 [],
                 filter_by_mask varying dd.dd_first_args ))
        in
        [push_after; push_enter]
      | None ->
        (* Cannot decompose — fall back to inline execution *)
        [Sasgn (Id.of_string "_result", None, e)]
    else (
      (* Single recursive call *)
        match
          check e
        with
      | Some cs ->
        (* Direct tail call — just push Enter *)
        let push_enter =
          make_stack_push
            (CPPstruct_id
               ( Id.of_string "_Enter",
                 [],
                 filter_by_mask varying cs.cs_args ))
        in
        [push_enter]
      | None ->
      match decompose_single_call check e with
      | Some d ->
        let push_combine =
          make_stack_push
            (CPPstruct_id (Id.of_string "_Combine", [], d.d_saved))
        in
        let push_enter =
          make_stack_push
            (CPPstruct_id
               ( Id.of_string "_Enter",
                 [],
                 filter_by_mask varying d.d_rec_args ))
        in
        [push_combine; push_enter]
      | None -> [Sasgn (Id.of_string "_result", None, e)] )
  | Sif (cond, then_br, else_br) ->
    let rw_then =
      List.concat_map (rewrite_multi_enter check varying) then_br
    in
    let rw_else =
      List.concat_map (rewrite_multi_enter check varying) else_br
    in
    rewrite_if_with_reuse_bypass check cond rw_then rw_else
  | Sblock stmts ->
    [Sblock (List.concat_map (rewrite_multi_enter check varying) stmts)]
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    [
      Scustom_case
        ( ty,
          scrut,
          tyargs,
          List.map
            (fun (ps, ret_ty, body) ->
              ( ps,
                ret_ty,
                List.concat_map (rewrite_multi_enter check varying) body ) )
            branches,
          err );
    ]
  | Sswitch (scrut, r, branches, default) ->
    [
      Sswitch
        ( scrut,
          r,
          List.map
            (fun (id, body) ->
              (id, List.concat_map (rewrite_multi_enter check varying) body) )
            branches,
          default );
    ]
  | Smatch (branches, default) ->
    [
      Smatch
        ( List.map
            (fun br ->
              { br with
                smb_body =
                  List.concat_map (rewrite_multi_enter check varying) br.smb_body })
            branches,
          Option.map
            (List.concat_map (rewrite_multi_enter check varying))
            default );
    ]
  | s -> [s]

(** Find the combining operation from the first double-call return in body. *)
let rec find_combine_op check stmts =
  List.find_map (find_combine_op_stmt check) stmts

(** Search a single statement for a double-call return and extract its
    combining operation. Statement-level companion of {!find_combine_op}. *)
and find_combine_op_stmt check = function
  | Sreturn (Some e) ->
    if count_calls_expr check e >= 2 then
      match
        decompose_double_call check e
      with
      | Some dd ->
        if dd.dd_saved = [] then
          Some (fun l r -> dd.dd_combine [] l r)
        else
          None
      | None -> None
    else
      None
  | Sif (_, then_br, else_br) ->
    ( match find_combine_op check then_br with
    | Some _ as r -> r
    | None -> find_combine_op check else_br )
  | Sblock stmts -> find_combine_op check stmts
  | Scustom_case (_, _, _, branches, _) ->
    List.find_map (fun (_, _, body) -> find_combine_op check body) branches
  | Sswitch (_, _, branches, _) ->
    List.find_map (fun (_, body) -> find_combine_op check body) branches
  | Smatch (branches, default) ->
    ( match List.find_map (fun br ->
        match br.smb_reuse with
        | Some (_, _, stmts) ->
          ( match find_combine_op check stmts with
          | Some _ as r -> r
          | None -> find_combine_op check br.smb_body )
        | None -> find_combine_op check br.smb_body) branches with
    | Some _ as r -> r
    | None -> match default with Some ss -> find_combine_op check ss | None -> None )
  | _ -> None

(** {3 Shared helpers for transform_multi and transform_nontail}

    Both multi-recursion and non-tail recursion transforms generate the same
    boilerplate: struct definitions, stack initialization, parameter copies
    from frame, frame lambdas, and the while-loop dispatch. These helpers
    factor out the common patterns. *)

(** Generate the initial [_stack.emplace_back(_Enter\{...\})] statement.

    @param varying_params The parameters to include in the Enter frame
    @return A raw C++ statement pushing the initial Enter frame *)
let make_stack_init varying_params =
  make_stack_push
    (CPPstruct_id
       ( Id.of_string "_Enter",
         [],
         List.map (fun (id, _) -> CPPvar id) varying_params ))

(** Generate parameter copy statements that read frame fields into locals.
    Produces [auto name = _f.name;] for each varying parameter.

    @param pp_type Type printer function
    @param varying_params The parameters to copy from the frame
    @return List of raw C++ assignment statements *)
let make_param_copies varying_params =
  List.map
    (fun (id, ty) ->
      Sasgn (id, Some (strip_ref_type ty),
             CPPmember (CPPvar (Id.of_string "_f"), id)))
    varying_params

(** Build one branch of the frame-dispatch [Smatch].

    The loop variable [_frame] is the scrutinee; the frame struct type is
    represented as [Tvar(0, Some name)] (avoids the struct-name qualification
    that [Tid] would add); [_f] is the [const auto&] binding that gives the
    handler body access to the saved frame fields.

    @param frame_name Name of the frame struct (e.g. ["_Enter"], ["_Call1"])
    @param body       Handler body statements
    @return An [smatch_branch] for use in [Smatch (branches, None)] *)
let make_frame_branch frame_name body =
  { smb_scrutinee = CPPvar (Id.of_string "_frame");
    smb_ctor_type = Tvar (0, Some (Id.of_string frame_name));
    smb_var = Some (Id.of_string "_f");
    smb_field_bindings = [];
    smb_extra_conds = [];
    smb_reuse = None;
    smb_is_value_type = false;
    smb_is_owned = true;
    smb_body = body }

(** Generate the while-loop body and surrounding boilerplate for the
    frame-dispatch loop.  Each iteration moves the top frame into a local,
    pops the stack, then dispatches via an [Smatch] if/else-if chain.

    @param struct_defs The struct definitions ([_Enter], [_CallN], etc.)
    @param ret_ty      Return type for the [_result] declaration
    @param init_push   The initial stack-push statement
    @param branches    One [smatch_branch] per frame type, in dispatch order
    @return Complete statement list for the loopified function body *)
let make_loop_and_return struct_defs ret_ty init_push branches =
  let result_decl = Sdecl_init (Id.of_string "_result", ret_ty) in
  (* Use Tvar with Some name to avoid struct-name qualification that Tid adds *)
  let frame_ty = Tvar (0, Some (Id.of_string "_Frame")) in
  (* std::vector<_Frame> has no AST representation — keep as Sraw *)
  let stack_decl = Sraw "std::vector<_Frame> _stack;\n  _stack.reserve(16);" in
  (* [Smatch (branches, None)] = exhaustive if/else-if chain; no wildcard needed
     since the variant can only hold the listed frame types. *)
  let dispatch_stmt = Smatch (branches, None) in
  let loop_body =
    [
      Sasgn (Id.of_string "_frame", Some frame_ty,
             CPPmove
               (CPPfun_call
                  (CPPmember (CPPvar (Id.of_string "_stack"),
                              Id.of_string "back"), [])));
      Sexpr
        (CPPfun_call
           (CPPmember (CPPvar (Id.of_string "_stack"),
                       Id.of_string "pop_back"), []));
      dispatch_stmt;
    ]
  in
  struct_defs
  @ [
      result_decl;
      stack_decl;
      init_push;
      Swhile
        (CPPunop ("!",
                  CPPfun_call
                    (CPPmember (CPPvar (Id.of_string "_stack"),
                                Id.of_string "empty"), [])),
         loop_body);
      Sreturn (Some (CPPvar (Id.of_string "_result")));
    ]

(** Transform a multi-recursive function body using frame-based stack.

    Generates Enter/After/Combine frame structs, a std::variant stack, and a
    while loop that dispatches via std::visit with Overloaded. *)
let transform_multi check _pp_type params ret_ty body =
  let varying = find_varying_params check params body in
  let varying_params = filter_by_mask varying params in
  let n_varying = List.length varying_params in
  (* Extract combine operation from first double-call site *)
  let combine_op =
    match find_combine_op check body with
    | Some op -> op
    | None ->
      (* Default to addition if we can't find it *)
      fun l r -> CPPbinop ("+", l, r)
  in
  (* Build struct definitions *)
  let enter_fields =
    List.map (fun (id, ty) -> (id, strip_ref_type ty)) varying_params
  in
  let after_fields =
    List.mapi
      (fun i (_, ty) -> (Id.of_string ("_a" ^ string_of_int i), strip_ref_type ty))
      varying_params
  in
  let enter_ty = Tvar (0, Some (Id.of_string "_Enter")) in
  let after_ty = Tvar (0, Some (Id.of_string "_After")) in
  let combine_ty = Tvar (0, Some (Id.of_string "_Combine")) in
  let struct_defs =
    [
      Sstruct_def (Id.of_string "_Enter", enter_fields);
      Sstruct_def (Id.of_string "_After", after_fields);
      Sstruct_def (Id.of_string "_Combine",
                   [(Id.of_string "_left", ret_ty)]);
      Susing (Id.of_string "_Frame",
              Tvariant [enter_ty; after_ty; combine_ty]);
    ]
  in
  let init_push = make_stack_init varying_params in
  (* Enter handler: copy frame fields to locals, then rewritten body *)
  let enter_body =
    make_param_copies varying_params
    @ List.concat_map (rewrite_multi_enter check varying) body
  in
  let enter_branch = make_frame_branch "_Enter" enter_body in
  (* After handler: push Combine{_result}, then Enter{_f._a0, ...} *)
  let after_enter_args =
    List.init n_varying (fun i ->
      CPPmember
        (CPPvar (Id.of_string "_f"), Id.of_string ("_a" ^ string_of_int i)))
  in
  let after_body =
    [
      make_stack_push
        (CPPstruct_id
           (Id.of_string "_Combine", [], [CPPvar (Id.of_string "_result")]));
      make_stack_push
        (CPPstruct_id (Id.of_string "_Enter", [], after_enter_args));
    ]
  in
  let after_branch = make_frame_branch "_After" after_body in
  (* Combine handler: _result = combine(_f._left, _result). Uses CPPbinop("=",
     ...) instead of Sasgn so lambda_needs_capture detects the _result reference
     and generates [&] capture. *)
  let combine_expr =
    combine_op
      (CPPmember (CPPvar (Id.of_string "_f"), Id.of_string "_left"))
      (CPPvar (Id.of_string "_result"))
  in
  let combine_body = assign_result combine_expr in
  let combine_branch = make_frame_branch "_Combine" combine_body in
  make_loop_and_return struct_defs ret_ty init_push
    [enter_branch; after_branch; combine_branch]

(** Rewrite variable references and field accesses on lambda-scoped variables
    to use std::declval, so that decltype expressions are valid at struct
    definition scope.  E.g., [_args.d_a0] becomes
    [std::declval<CtorType&>().d_a0] and plain [b] becomes
    [std::declval<unsigned int&>()]. *)
let rec rewrite_field_access_for_decltype pp_type env expr =
  match expr with
  | CPPvar id ->
    ( match lookup_var_type env id with
    | Some ty ->
      let base_ty = strip_ref_type ty in
      CPPraw ("std::declval<" ^ pp_type base_ty ^ "&>()")
    | None -> expr )
  | CPPget (CPPvar id, field) ->
    (* Dot access on a variable.  Strip const to get the struct type for
       std::declval. *)
    ( match lookup_var_type env id with
    | Some ty ->
      let base_ty = strip_ref_type ty in
      let struct_ty =
        match base_ty with
        | Tmod (TMconst, t) -> t
        | t -> t
      in
      CPPraw ("std::declval<" ^ pp_type struct_ty ^ "&>()." ^ Id.to_string field)
    | None -> expr )
  | CPParrow (CPPvar id, field) ->
    (* Arrow access on a pointer variable — used by Smatch bindings
       ([_m->d_field] from [std::get_if]) and loopify frame dispatch. *)
    ( match lookup_var_type env id with
    | Some ty ->
      let base_ty = strip_ref_type ty in
      let pointee_ty =
        match base_ty with
        | Tptr (Tmod (TMconst, t)) | Tptr t -> t
        | t -> t
      in
      CPPraw ("std::declval<" ^ pp_type pointee_ty ^ "&>()." ^ Id.to_string field)
    | None -> expr )
  | _ ->
    map_expr (rewrite_field_access_for_decltype pp_type env) Fun.id Fun.id expr

(** Build a [Tdecltype(expr)] type, suitable for struct field type annotations
    when the actual type is unknown. Rewrites variable references to use
    std::declval so that decltype is valid at struct definition scope. *)
let make_decltype_ty pp_type env expr =
  let expr = rewrite_field_access_for_decltype pp_type env expr in
  Tdecltype expr

(** Transform a non-tail recursive function body using an explicit frame-based stack.

    Non-tail recursion requires saving continuation context. We use typed frames
    stored in a [std::variant] stack. Each frame captures the state needed to
    resume after a recursive call returns.

    {v
    let rec f x = if base(x) then result else combine(x, f(next(x)))

    becomes:

    struct _Enter { T x; };
    struct _Call1 { T _s0; };  // saves 'x' for combine step
    using _Frame = std::variant<_Enter, _Call1>;

    let f x_init =
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{x_init});
      T _result;
      while (!_stack.empty()) {
        std::visit(Overloaded{
          [&](_Enter _f) {
            if (base(_f.x)) { _result = result; }
            else {
              _stack.emplace_back(_Call1{_f.x});      // save x
              _stack.emplace_back(_Enter{next(_f.x)});  // recurse
            }
          },
          [&](_Call1 _f) { _result = combine(_f._s0, _result); }
        }, _stack.back());
        _stack.pop_back();
      }
      return _result;
    v}

    Frame types:
    - [_Enter]: Captures function arguments (the "call" part of a recursive call)
    - [_CallN]: Captures continuation context (values needed after a call returns)

    The transformation:
    1. Identifies varying vs invariant parameters
    2. Rewrites [_Enter] handler: returns → frame pushes
    3. Collects [_CallN] frame info during rewriting
    4. Generates frame struct definitions
    5. Generates dispatch loop with [std::visit]

    @param check Call checker for identifying recursive calls
    @param pp_type Type pretty-printer
    @param pp_expr Expression pretty-printer
    @param tparams Template parameter context
    @param params Function parameters
    @param ret_ty Return type
    @param body Function body
    @return Transformed body with frame-based stack structure *)
let transform_nontail check pp_type _pp_expr tparams params ret_ty body =
  let varying = find_varying_params check params body in
  let varying_params = filter_by_mask varying params in
  let varying_param_types = List.map snd varying_params in
  (* Build initial type env from params and body declarations *)
  let env =
    collect_type_env body @ List.map (fun (id, ty) -> (id, ty)) params
  in
  (* Rewrite body for Enter handler and collect call frame info *)
  let call_counter = ref 1 in
  let frames_ref = ref [] in
  let rewritten_body =
    List.map
      (rewrite_enter_stmt
         check varying tparams env ret_ty pp_type
         call_counter frames_ref varying_param_types)
      body
  in
  (* Sort frames by name to ensure consistent ordering *)
  let frames =
    List.sort (fun a b -> String.compare a.cf_name b.cf_name) !frames_ref
  in
  (* Build struct definitions *)
  let enter_fields =
    List.map (fun (id, ty) -> (id, strip_ref_type ty)) varying_params
  in
  let call_structs =
    List.map
      (fun cf ->
        let fields =
          List.mapi
            (fun j ty ->
              let field_ty =
                match ty with
                | Tunknown ->
                  let expr = List.nth cf.cf_saved_exprs j in
                  make_decltype_ty pp_type cf.cf_env expr
                | _ -> strip_ref_type ty
              in
              (Id.of_string ("_s" ^ string_of_int j), field_ty))
            cf.cf_saved_types
        in
        Sstruct_def (Id.of_string cf.cf_name, fields))
      frames
  in
  let call_names = List.map (fun cf -> cf.cf_name) frames in
  let enter_ty = Tvar (0, Some (Id.of_string "_Enter")) in
  let variant_tys =
    enter_ty
    :: List.map (fun name -> Tvar (0, Some (Id.of_string name))) call_names
  in
  let struct_defs =
    [Sstruct_def (Id.of_string "_Enter", enter_fields)]
    @ call_structs
    @ [Susing (Id.of_string "_Frame", Tvariant variant_tys)]
  in
  let init_push = make_stack_init varying_params in
  (* Enter handler: copy frame fields to locals (only varying params; invariant
     params are captured directly from function scope) *)
  let enter_body = make_param_copies varying_params @ rewritten_body in
  let enter_branch = make_frame_branch "_Enter" enter_body in
  (* Call handlers *)
  let call_branches =
    List.map (fun cf -> make_frame_branch cf.cf_name cf.cf_handler) frames
  in
  make_loop_and_return struct_defs ret_ty init_push (enter_branch :: call_branches)

(** {2 Main transformation dispatch} *)

(** {3 Generic AST predicate search} *)

(** Check if any expression in a statement list satisfies [pred]. Descends into
    all branches, lambdas, and sub-expressions. *)
let rec body_has_expr pred stmts = List.exists (stmt_has_expr pred) stmts

(** Check if a single statement contains an expression satisfying [pred].
    Statement-level companion of {!body_has_expr}. *)
and stmt_has_expr pred = function
  | Sreturn (Some e) -> expr_has pred e
  | Sreturn None -> false
  | Sdecl _ -> false
  | Sasgn (_, _, e) | Sderef_asgn (_, e) -> expr_has pred e
  | Sexpr e -> expr_has pred e
  | Sif (cond, then_br, else_br) ->
    expr_has pred cond
    || body_has_expr pred then_br
    || body_has_expr pred else_br
  | Scustom_case (_, scrut, _, branches, _) ->
    expr_has pred scrut
    || List.exists (fun (_, _, body) -> body_has_expr pred body) branches
  | Sswitch (e, _, branches, _) ->
    expr_has pred e
    || List.exists (fun (_, body) -> body_has_expr pred body) branches
  | Swhile (cond, body) -> expr_has pred cond || body_has_expr pred body
  | Sblock stmts -> body_has_expr pred stmts
  | Sassign_field (obj, _, e) -> expr_has pred obj || expr_has pred e
  | Sblock_custom (_, _, _, _, args, _) ->
    List.exists (expr_has pred) args
  | Smatch (branches, default) ->
    List.exists (fun br ->
      expr_has pred br.smb_scrutinee
      || List.exists (expr_has pred) br.smb_extra_conds
      || ( match br.smb_reuse with
         | Some (cond, _, stmts) -> expr_has pred cond || body_has_expr pred stmts
         | None -> false )
      || body_has_expr pred br.smb_body) branches
    || (match default with Some s -> body_has_expr pred s | None -> false)
  | Sthrow _ | Sassert _ | Sraw _ | Sstruct_def _ | Susing _ | Sdecl_init _
  | Scontinue | Sbreak -> false

(** Check if an expression or any of its sub-expressions satisfies [pred].
    Expression-level companion of {!body_has_expr}. *)
and expr_has pred = function
  | e when pred e -> true
  | CPPfun_call (f, args) -> expr_has pred f || List.exists (expr_has pred) args
  | CPPmethod_call (obj, _, args) ->
    expr_has pred obj || List.exists (expr_has pred) args
  | CPPbinop (_, e1, e2) -> expr_has pred e1 || expr_has pred e2
  | CPPmove e | CPPderef e | CPPforward (_, e) | CPPnamespace (_, e) ->
    expr_has pred e
  | CPPlambda (_, _, body, _) -> body_has_expr pred body
  | CPPoverloaded exprs -> List.exists (expr_has pred) exprs
  | CPPget (e, _)
   |CPPget' (e, _)
   |CPPmember (e, _)
   |CPParrow (e, _)
   |CPPqualified (e, _) -> expr_has pred e
  | CPPstruct (_, _, args) | CPPstructmk (_, _, args) | CPPstruct_id (_, _, args)
    -> List.exists (expr_has pred) args
  | _ -> false

(** Check if a function body contains any call to a function identified by
    [target_id]. Searches through all statements and nested expressions for a
    [CPPfun_call (CPPvar id, _)] where [id] equals [target_id].

    @param target_id The function name to search for
    @param stmts     The statement list (function body) to search
    @return [true] if any call to [target_id] is found *)
let body_calls_id target_id stmts =
  body_has_expr
    (function
      | CPPfun_call (CPPvar id, _) when Id.equal id target_id -> true
      | _ -> false )
    stmts

(** {3 GlobRef-based mutual recursion} *)

(** Check if a function body calls any function whose [GlobRef.t] appears in
    [refs]. Searches through all statements and nested expressions for a
    [CPPfun_call (CPPglob (r, _, _), _)] where [r] matches any element of [refs].

    Used in mutual recursion detection to determine whether a callee calls back
    into the current function.

    @param refs List of [GlobRef.t] values to check for
    @param body The statement list (function body) to search
    @return [true] if any call to a ref in [refs] is found *)
let body_calls_any_ref refs body =
  let eq r sr = Environ.QGlobRef.equal Environ.empty_env r sr in
  body_has_expr
    (function
      | CPPfun_call (CPPglob (r, _, _), _) when List.exists (eq r) refs -> true
      | _ -> false )
    body

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
     in the body, check if the callee is registered AND the callee calls back
     this function (true mutual recursion). *)
  let self_refs = List.map fst names in
  (* Check if a GlobRef or Id matches a registered function *)
  let find_registered_callee_by_ref r =
    if
      List.exists
        (fun sr -> Environ.QGlobRef.equal Environ.empty_env r sr)
        self_refs
    then
      None
    else
      match
        Hashtbl.find_opt mutual_fn_table r
      with
      | Some (callee_params, callee_body)
        when body_calls_any_ref self_refs callee_body ->
        Some (r, callee_params, callee_body)
      | _ -> None
  in
  let find_registered_callee_by_id id =
    Hashtbl.fold
      (fun r (callee_params, callee_body) acc ->
        match acc with
        | Some _ -> acc
        | None ->
          if
            List.exists
              (fun sr -> Environ.QGlobRef.equal Environ.empty_env r sr)
              self_refs
          then
            None
          else
            let label =
              match r with
              | GlobRef.ConstRef c -> Label.to_id (Constant.label c)
              | GlobRef.VarRef v -> v
              | _ -> Id.of_string ""
            in
            if Id.equal id label && body_calls_any_ref self_refs callee_body
            then
              Some (r, callee_params, callee_body)
            else
              None )
      mutual_fn_table
      None
  in
  let rec find_callee_in_expr expr =
    match expr with
    | CPPfun_call (CPPglob (r, _, _), _) ->
      ( match find_registered_callee_by_ref r with
      | Some _ as result -> result
      | None -> None )
    | CPPfun_call (CPPvar id, _) ->
      ( match find_registered_callee_by_id id with
      | Some _ as result -> result
      | None -> None )
    | CPPfun_call (_, args) -> List.find_map find_callee_in_expr args
    | CPPbinop (_, e1, e2) ->
      ( match find_callee_in_expr e1 with
      | Some _ as r -> r
      | None -> find_callee_in_expr e2 )
    | CPPmove e | CPPderef e | CPPnamespace (_, e) -> find_callee_in_expr e
    | CPPlambda (_, _, stmts, _) -> find_callee_in_stmts stmts
    | CPPoverloaded es -> List.find_map find_callee_in_expr es
    | _ -> None
  and find_callee_in_stmts stmts = List.find_map find_callee_in_stmt stmts
  and find_callee_in_stmt = function
    | Sreturn (Some e) -> find_callee_in_expr e
    | Sasgn (_, _, e) | Sderef_asgn (_, e) | Sexpr e -> find_callee_in_expr e
    | Sif (_, t, e) ->
      ( match find_callee_in_stmts t with
      | Some _ as r -> r
      | None -> find_callee_in_stmts e )
    | Scustom_case (_, scrut, _, branches, _) ->
      ( match find_callee_in_expr scrut with
      | Some _ as r -> r
      | None -> List.find_map (fun (_, _, b) -> find_callee_in_stmts b) branches
      )
    | Smatch (branches, default) ->
      ( match List.find_map (fun br ->
          match br.smb_reuse with
          | Some (_, _, stmts) ->
            ( match find_callee_in_stmts stmts with
            | Some _ as r -> r
            | None -> find_callee_in_stmts br.smb_body )
          | None -> find_callee_in_stmts br.smb_body) branches with
      | Some _ as r -> r
      | None -> match default with Some ss -> find_callee_in_stmts ss | None -> None )
    | Sblock ss -> find_callee_in_stmts ss
    | _ -> None
  in
  match find_callee_in_stmts body with
  | None -> body
  | Some (callee_ref, callee_params, callee_body) ->
    (* Generate fresh parameter names to avoid collision with outer function *)
    let rename_map =
      List.map
        (fun (pid, _ty) -> (pid, Id.of_string ("_inl_" ^ Id.to_string pid)))
        callee_params
    in
    let fresh_params =
      List.map (fun (pid, ty) -> (List.assoc pid rename_map, ty)) callee_params
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
      | CPPfun_call (CPPglob (r, _, _), _)
        when Environ.QGlobRef.equal Environ.empty_env r callee_ref -> true
      | CPPfun_call (CPPvar id, _) when Id.equal id callee_label -> true
      | _ -> false
    in
    let get_call_args = function
      | CPPfun_call (_, args) -> args
      | _ -> []
    in
    let rec inline_stmts stmts = List.concat_map inline_stmt stmts
    and inline_stmt = function
      | Sreturn (Some e) when is_callee_call e ->
        (* Tail call to callee — inline body with param bindings *)
        let bindings =
          List.map2
            (fun (pid, ty) arg -> Sasgn (pid, Some ty, arg))
            fresh_params
            (get_call_args e)
        in
        bindings @ fresh_body
      | Sif (cond, then_br, else_br) ->
        [Sif (cond, inline_stmts then_br, inline_stmts else_br)]
      | Scustom_case (ty, scrut, tyargs, branches, err) ->
        [
          Scustom_case
            ( ty,
              inline_expr scrut,
              tyargs,
              List.map (fun (ps, rty, b) -> (ps, rty, inline_stmts b)) branches,
              err );
        ]
      | Sreturn (Some e) -> [Sreturn (Some (inline_expr e))]
      | Sasgn (id, ty, e) -> [Sasgn (id, ty, inline_expr e)]
      | Sderef_asgn (id, e) -> [Sderef_asgn (id, inline_expr e)]
      | Sexpr e -> [Sexpr (inline_expr e)]
      | Smatch (branches, default) ->
        [
          Smatch
            ( List.map
                (fun br -> { br with smb_body = inline_stmts br.smb_body })
                branches,
              Option.map inline_stmts default );
        ]
      | Sblock ss -> [Sblock (inline_stmts ss)]
      | s -> [s]
    and inline_expr expr =
      if is_callee_call expr then
        (* Non-tail call — wrap in immediately-invoked lambda *)
        let lparams = List.map (fun (pid, ty) -> (ty, Some pid)) fresh_params in
        CPPfun_call
          (CPPlambda (lparams, None, fresh_body, true), get_call_args expr)
      else
        map_expr
          inline_expr
          (fun s ->
            match inline_stmt s with
            | [s'] -> s'
            | ss -> Sblock ss )
          Fun.id
          expr
    in
    inline_stmts body

(** {2 Inner lambda loopification}

    Transforms self-recursive [std::function] lambdas within function bodies
    into iterative versions using the same while-loop or stack-frame techniques
    as top-level functions. *)

(** Create a {!call_checker} that recognises self-recursive calls within an
    inner lambda. Matches [CPPfun_call (CPPvar id, args)] where [id] equals
    [lambda_name]. All matched calls are marked as non-tail since inner lambda
    calls are processed within expression contexts.

    @param lambda_name The [Id.t] name of the lambda variable (e.g., the [id]
                       in [std::function<...> id = ...])
    @return A {!call_checker} suitable for {!classify}, {!transform_tail}, etc. *)
let lambda_checker (lambda_name : Id.t) : call_checker =
 fun e ->
   match e with
   | CPPfun_call (CPPvar id, args) when Id.equal id lambda_name ->
     (* Direct call: [f(args)] — by-reference fixpoint pattern *)
     Some {cs_args = args; cs_is_tail = false}
   | CPPfun_call (CPPderef (CPPvar id), args) when Id.equal id lambda_name ->
     (* Dereferenced call — shared_ptr fixpoint pattern *)
     Some {cs_args = args; cs_is_tail = false}
   | _ -> None

(** Walk through a statement list and loopify any self-recursive [std::function]
    lambda assignments.

    Recognises two patterns for self-recursive lambdas:
    + [Sdecl(id, Tfun _); Sasgn(id, None, CPPlambda(...))] -- declaration
      followed by assignment (common when Coq's [let fix] is extracted).
    + [Sasgn(id, Some(Tfun _), CPPlambda(...))] -- combined declaration and
      assignment.

    For each matched lambda whose body contains recursive calls to [id] (as
    determined by {!lambda_checker} and {!classify}), applies the appropriate
    transformation ({!transform_tail}, {!transform_multi}, or
    {!transform_nontail}). Lambdas without self-recursion are left unchanged but
    their bodies are recursively scanned for nested lambdas.

    Also descends into all nested statement structures (if/else, while loops,
    [std::visit] lambdas, switch, blocks) and into lambda expressions within
    assignments and returns, to find recursive lambda patterns at any depth.

    @param pp_type  Type pretty-printer (threaded to transformation functions)
    @param pp_expr  Expression pretty-printer (threaded to {!transform_nontail})
    @param tparams  Type parameters of the enclosing function
    @param body     The statement list to scan and transform
    @return The statement list with all self-recursive inner lambdas loopified *)
let loopify_inner_lambdas ~pp_type ~pp_expr ~tparams body =
  let try_loopify_lambda id lparams ret_ty_opt lbody cap =
    let check = lambda_checker id in
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
      let lbody' =
        match kind with
        | Tail_recursion -> transform_tail check pp_type params ret_ty lbody
        | Nontail_recursion ->
          if
            has_multi_call_expr check lbody
            && not (has_triple_call_expr check lbody)
          then
            transform_multi check pp_type params ret_ty lbody
          else
            transform_nontail check pp_type pp_expr tparams params ret_ty lbody
        | No_recursion -> assert false
      in
      Some lbody'
  in
  let rec process_stmts stmts =
    match stmts with
    | [] -> []
    (* Pattern 1: Sdecl(id, Tfun _) followed by Sasgn(id, None,
       CPPlambda(...)) *)
    | Sdecl (id, (Tfun _ as decl_ty))
      :: Sasgn (id2, None, CPPlambda (lparams, ret_ty_opt, lbody, cap))
      :: rest
      when Id.equal id id2 ->
      ( match try_loopify_lambda id lparams ret_ty_opt lbody cap with
      | Some lbody' ->
        Sdecl (id, decl_ty)
        :: Sasgn (id, None, CPPlambda (lparams, ret_ty_opt, lbody', cap))
        :: process_stmts rest
      | None ->
        let lbody' = process_stmts lbody in
        Sdecl (id, decl_ty)
        :: Sasgn (id, None, CPPlambda (lparams, ret_ty_opt, lbody', cap))
        :: process_stmts rest )
    (* Pattern 2: Sasgn(id, Some(Tfun _), CPPlambda(...)) — combined
       decl+assign *)
    | Sasgn
        ( id,
          (Some (Tfun _) as ty_opt),
          CPPlambda (lparams, ret_ty_opt, lbody, cap) )
      :: rest ->
      ( match try_loopify_lambda id lparams ret_ty_opt lbody cap with
      | Some lbody' ->
        Sasgn (id, ty_opt, CPPlambda (lparams, ret_ty_opt, lbody', cap))
        :: process_stmts rest
      | None ->
        let lbody' = process_stmts lbody in
        Sasgn (id, ty_opt, CPPlambda (lparams, ret_ty_opt, lbody', cap))
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
    | Sasgn (id, (Some Tauto as _ty_opt),
             (CPPfun_call (CPPmk_shared func_ty, []) as init_expr))
      :: Sderef_asgn (id2, CPPlambda (lparams, ret_ty_opt, lbody, cap))
      :: rest
      when Id.equal id id2 ->
      ( match try_loopify_lambda id lparams ret_ty_opt lbody cap with
      | Some lbody' ->
        Sdecl (id, func_ty)
        :: Sasgn (id, None, CPPlambda (lparams, ret_ty_opt, lbody', false))
        :: process_stmts (un_deref_var_stmts id rest)
      | None ->
        let lbody' = process_stmts lbody in
        Sasgn (id, _ty_opt, init_expr)
        :: Sderef_asgn (id, CPPlambda (lparams, ret_ty_opt, lbody', cap))
        :: process_stmts rest )
    | stmt :: rest -> process_stmt stmt :: process_stmts rest
  and process_expr expr =
    match expr with
    | CPPlambda (lp, rt, body, cap) ->
      CPPlambda (lp, rt, process_stmts body, cap)
    | CPPoverloaded es -> CPPoverloaded (List.map process_expr es)
    | CPPfun_call (f, args) ->
      CPPfun_call (process_expr f, List.map process_expr args)
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
    | Smatch (branches, default) ->
      Smatch
        ( List.map
            (fun br ->
              { br with
                smb_scrutinee = process_expr br.smb_scrutinee;
                smb_extra_conds = List.map process_expr br.smb_extra_conds;
                smb_reuse =
                  Option.map (fun (cond, rf, stmts) ->
                    (process_expr cond, rf, process_stmts stmts)) br.smb_reuse;
                smb_body = process_stmts br.smb_body })
            branches,
          Option.map process_stmts default )
    | Swhile (cond, body) -> Swhile (process_expr cond, process_stmts body)
    | Sexpr e -> Sexpr (process_expr e)
    | Sasgn (id, ty, e) -> Sasgn (id, ty, process_expr e)
    | Sderef_asgn (id, e) -> Sderef_asgn (id, process_expr e)
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
          CPPqualified(type_expr, "lazy_"),
          [CPPlambda([], Some ret_ty, inner_body, capture)])))
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
  | Some (Sreturn (Some (CPPfun_call (
      CPPqualified (_, lazy_id),
      [CPPlambda ([], Some _, _, _)]))))
    when Id.to_string lazy_id = "lazy_" -> true
  | _ -> false

let rec expr_contains_lazy_factory = function
  | CPPfun_call (CPPqualified (_, lazy_id), _) when Id.to_string lazy_id = "lazy_" ->
    true
  | e ->
    let found = ref false in
    let mark_expr e' =
      if expr_contains_lazy_factory e' then found := true;
      e'
    in
    let mark_stmt s =
      if stmt_contains_lazy_factory s then found := true;
      s
    in
    ignore (map_expr mark_expr mark_stmt Fun.id e);
    !found
and stmt_contains_lazy_factory s =
  let found = ref false in
  let mark_expr e =
    if expr_contains_lazy_factory e then found := true;
    e
  in
  let mark_stmt s' =
    if stmt_contains_lazy_factory s' then found := true;
    s'
  in
  ignore (map_stmt mark_expr mark_stmt Fun.id s);
  !found

let body_contains_lazy_factory body =
  List.exists stmt_contains_lazy_factory body

(** Transform a top-level function definition by loopifying its body.

    This is the main entry point for loopifying a [Dfundef]. The transformation
    proceeds in four steps:

    + Register the function in {!mutual_fn_table} so that other functions can
      detect mutual recursion with it.
    + Try to inline mutual recursion partners via {!try_inline_mutual_into},
      converting mutual recursion into self-recursion.
    + Classify the recursion pattern with {!classify} and apply the appropriate
      strategy: {!transform_tail} for tail recursion, {!transform_multi} for
      double-call expressions, or {!transform_nontail} for the general case.
    + Post-pass with {!loopify_inner_lambdas} to loopify any self-recursive
      [std::function] lambdas nested within the body.

    For cofixpoints returning a coinductive type, the body is wrapped in a
    [lazy_] thunk by [cofix_wrap].  The recursive calls are captured inside
    the closure and never executed at call time, so the function returns in
    O(1) stack frames and loopification is unnecessary.  We detect the
    [lazy_] pattern via {!has_lazy_body} and skip the main loopification
    pass.  See the {!has_lazy_body} section header for the full rationale.

    @param pp_type  Type pretty-printer
    @param pp_expr  Expression pretty-printer
    @param tparams  Type parameters of the function
    @param names    List of [(GlobRef.t, Id.t)] pairs identifying the function
    @param ret_ty   Return type
    @param params   Parameter list [(Id.t * cpp_type)]
    @param body     Original function body (statement list)
    @return A [Dfundef] declaration with the loopified body *)
let transform_fundef ~pp_type ~pp_expr ~tparams names ret_ty params body no_pure =
  (* Register this function for mutual recursion detection *)
  register_fundef names params body;
  (* Try to inline mutual recursion partners *)
  let body = try_inline_mutual_into names body in
  let check = fn_checker names in
  (* Cofixpoint guard: if this function body ends with a [lazy_] return,
     it is a cofixpoint returning a standard coinductive type.  The entire
     body (including recursive calls) is captured inside a [=] lambda and
     never executed at call time — the function returns a thunk in O(1)
     stack frames.  Loopification is unnecessary and TMC would generate
     invalid [v_mut()] calls (see the {!has_lazy_body} section header for
     the full rationale).  We still run [loopify_inner_lambdas] to handle
     any nested [std::function] fixpoints inside the lazy thunk. *)
  let body =
    if has_lazy_body body || body_contains_lazy_factory body then
      loopify_inner_lambdas ~pp_type ~pp_expr ~tparams body
    else
      (* Normal (non-lazy) function — existing path *)
      let kind = classify check body in
      let body =
        match kind with
        | No_recursion -> body
        | Tail_recursion -> transform_tail check pp_type params ret_ty body
        | Nontail_recursion ->
          if has_higher_order_template_param tparams
             && count_calls_stmts check body >= 2
          then
            body
          else
          ( match try_tmc_classify check body with
          | Some ti ->
            transform_tmc check pp_expr ti params ret_ty body
          | None ->
            if has_multi_call_expr check body
               && not (has_triple_call_expr check body)
            then
              transform_multi check pp_type params ret_ty body
            else
              transform_nontail check pp_type pp_expr tparams params ret_ty body )
      in
      loopify_inner_lambdas ~pp_type ~pp_expr ~tparams body
  in
  Dfundef (names, ret_ty, params, body, no_pure)

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
      loop, since the [_Enter] frame references [_self] by name.

    @param pp_type        Type pretty-printer
    @param pp_expr        Expression pretty-printer
    @param tparams        Type parameters
    @param self_ty        C++ type for the struct pointer (e.g.,
                          [Tmod (TMconst, Tptr (Tglob (...)))])
    @param mf             The method record to transform
    @return An [Fmethod] field with the loopified body *)
let transform_method ~pp_type ~pp_expr ~tparams ~self_ty mf =
  let n_params = List.length mf.mf_params in
  let this_pos = mf.mf_this_pos in
  (* Cofixpoint guard: same reasoning as {!transform_fundef} — if the
     method body is [lazy_]-wrapped, the entire body is deferred inside a
     closure and the method returns in O(1) stack frames.  Loopification
     is unnecessary and TMC would be invalid.  See {!has_lazy_body}. *)
  if has_lazy_body mf.mf_body then
    Fmethod mf
  else
    let basic_check = method_checker ~n_params ~has_self_param:false ~this_pos mf.mf_name in
    ( match classify basic_check mf.mf_body with
    | No_recursion -> Fmethod mf
    | (Tail_recursion | Nontail_recursion) as kind ->
      let self_id = Id.of_string "_self" in
      let body_with_self = List.map (this_to_self_stmt self_id) mf.mf_body in
      let self_param = (self_id, self_ty) in
      let augmented_params = self_param :: mf.mf_params in
      let self_check = method_checker ~n_params ~has_self_param:true ~this_pos mf.mf_name in
      let body', needs_init_self =
        match kind with
        | Tail_recursion ->
          ( transform_tail
              ~param_inits:[(self_id, CPPthis)]
              self_check
              pp_type
              augmented_params
              mf.mf_ret_type
              body_with_self,
            false )
        | Nontail_recursion ->
          ( match try_tmc_classify self_check body_with_self with
          | Some ti ->
            ( transform_tmc
                ~param_inits:[(self_id, CPPthis)]
                self_check
                pp_expr
                ti
                augmented_params
                mf.mf_ret_type
                body_with_self,
              false )
          | None ->
            ( ( if
                  has_multi_call_expr self_check body_with_self
                  && not (has_triple_call_expr self_check body_with_self)
                then
                  transform_multi
                    self_check
                    pp_type
                    augmented_params
                    mf.mf_ret_type
                    body_with_self
                else
                  transform_nontail
                    self_check
                    pp_type
                    pp_expr
                    tparams
                    augmented_params
                    mf.mf_ret_type
                    body_with_self ),
              true ) )
        | No_recursion -> assert false
      in
      if needs_init_self then
        let init_self = Sasgn (self_id, Some self_ty, CPPthis) in
        Fmethod {mf with mf_body = init_self :: body'}
      else
        Fmethod {mf with mf_body = body'} )

(** Transform a single struct field, loopifying it if it is a method.

    Non-method fields (e.g., [Ffield], [Ftype]) are returned unchanged. For
    [Fmethod] fields, delegates to {!transform_method}.

    @param pp_type        Type pretty-printer
    @param pp_expr        Expression pretty-printer
    @param tparams        Type parameters
    @param self_ty        C++ type for the struct pointer (e.g., [Tmod (TMconst, Tptr (Tglob (...)))])
    @param (fld, vis, tag) The field, its visibility, and optional tag
    @return The (possibly transformed) field triple *)
let transform_field ~pp_type ~pp_expr ~tparams ~self_ty (fld, vis, tag) =
  match fld with
  | Fmethod mf ->
    (transform_method ~pp_type ~pp_expr ~tparams ~self_ty mf, vis, tag)
  | _ -> (fld, vis, tag)

(** {2 Mutual recursion inlining}

    When two functions A and B call each other (mutual recursion), inline B's
    body at each call site in A. After inlining, A becomes self-recursive and
    can be loopified normally. B remains unchanged — it calls the (now
    loopified) A. *)

(** Substitute calls to [target_id] in a statement list with inlined body.
    [target_params] and [target_body] describe the function being inlined. *)
let rec inline_id_in_stmts target_id target_params target_body stmts =
  List.concat_map (inline_id_in_stmt target_id target_params target_body) stmts

(** Inline a function body into a single statement. Handles tail calls
    (direct substitution) and recurses into branches. Statement-level
    companion of {!inline_id_in_stmts}. *)
and inline_id_in_stmt target_id target_params target_body stmt =
  match stmt with
  | Sreturn (Some (CPPfun_call (CPPvar id, args))) when Id.equal id target_id ->
    (* Direct tail call — inline with parameter substitution *)
    let param_bindings =
      List.map2
        (fun (pid, ty) arg -> Sasgn (pid, Some ty, arg))
        target_params
        args
    in
    param_bindings @ target_body
  | Sif (cond, then_br, else_br) ->
    [
      Sif
        ( cond,
          inline_id_in_stmts target_id target_params target_body then_br,
          inline_id_in_stmts target_id target_params target_body else_br );
    ]
  | Sreturn (Some e) ->
    [Sreturn (Some (inline_id_in_expr target_id target_params target_body e))]
  | Sasgn (id, ty, e) ->
    [Sasgn (id, ty, inline_id_in_expr target_id target_params target_body e)]
  | Sderef_asgn (id, e) ->
    [Sderef_asgn (id, inline_id_in_expr target_id target_params target_body e)]
  | Sexpr e -> [Sexpr (inline_id_in_expr target_id target_params target_body e)]
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    [
      Scustom_case
        ( ty,
          inline_id_in_expr target_id target_params target_body scrut,
          tyargs,
          List.map
            (fun (ps, rty, body) ->
              ( ps,
                rty,
                inline_id_in_stmts target_id target_params target_body body ) )
            branches,
          err );
    ]
  | Smatch (branches, default) ->
    let rw = inline_id_in_stmts target_id target_params target_body in
    [
      Smatch
        ( List.map
            (fun br -> { br with smb_body = rw br.smb_body })
            branches,
          Option.map rw default );
    ]
  | Sblock stmts ->
    [Sblock (inline_id_in_stmts target_id target_params target_body stmts)]
  | _ -> [stmt]

(** Inline a function body into an expression. Non-tail calls are wrapped
    in an immediately-invoked lambda (IIFE). Expression-level companion
    of {!inline_id_in_stmts}. *)
and inline_id_in_expr target_id target_params target_body expr =
  match expr with
  | CPPfun_call (CPPvar id, args) when Id.equal id target_id ->
    (* Non-tail call — wrap inlined body in immediately-invoked lambda *)
    let new_params = List.map (fun (pid, ty) -> (ty, Some pid)) target_params in
    CPPfun_call (CPPlambda (new_params, None, target_body, true), args)
  | _ ->
    map_expr
      (inline_id_in_expr target_id target_params target_body)
      (fun s ->
        match inline_id_in_stmt target_id target_params target_body s with
        | [s'] -> s'
        | stmts -> Sblock stmts )
      Fun.id
      expr

(** Try to inline mutual recursion among Ffundef fields in a struct. Returns the
    modified field list. *)
let try_inline_mutual_fields fields =
  (* Extract Ffundef entries *)
  let fundefs =
    List.filter_map
      (fun (f, _, _) ->
        match f with
        | Ffundef (name, ret_ty, params, body) ->
          Some (name, ret_ty, params, body)
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
    let name_b, _ret_ty_b, params_b, body_b = List.nth fundefs j in
    (* Inline B into A *)
    List.map
      (fun (f, vis, tag) ->
        match f with
        | Ffundef (name, ret_ty, params, body) when Id.equal name name_a ->
          let new_body = inline_id_in_stmts name_b params_b body_b body in
          (Ffundef (name, ret_ty, params, new_body), vis, tag)
        | _ -> (f, vis, tag) )
      fields

(** Top-level entry point: transform a declaration and all its nested
    declarations (templates, structs, namespaces). Dispatches to
    {!transform_fundef}, {!transform_method}, or recurses for composite
    declarations. *)
let rec transform_decl ?(tparams = []) ~pp_type ~pp_expr = function
  | Dtemplate (tparams, constraint_opt, inner) ->
    Dtemplate
      (tparams, constraint_opt, transform_decl ~tparams ~pp_type ~pp_expr inner)
  | Dfundef (names, ret_ty, params, body, no_pure) ->
    transform_fundef ~pp_type ~pp_expr ~tparams names ret_ty params body no_pure
  | Dstruct ds ->
    let self_ty = Tmod (TMconst, Tptr (Tglob (ds.ds_ref, [], []))) in
    (* Try inlining mutual recursion among struct fields before transforms *)
    let fields = try_inline_mutual_fields ds.ds_fields in
    Dstruct
      {
        ds with
        ds_fields =
          List.map
            (transform_field ~pp_type ~pp_expr ~tparams ~self_ty)
            fields;
      }
  | Dnspace (r, decls) ->
    (* Pre-register all functions for mutual recursion detection before
       transforming *)
    List.iter
      (function
        | Dfundef (names, _, params, body, _) -> register_fundef names params body
        | Dtemplate (_, _, Dfundef (names, _, params, body, _)) ->
          register_fundef names params body
        | _ -> () )
      decls;
    Dnspace (r, List.map (transform_decl ~tparams ~pp_type ~pp_expr) decls)
  | d -> d
