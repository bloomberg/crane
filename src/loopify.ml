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

(** {3 Generic mutual recursion inlining}

    Every inlining Loopify does is one operation: find every call to a
    target function and replace it with the callee's body.  This record and
    the three generic traversal functions capture it, parameterised only by
    how the calls inlined are recognised. *)

(** How an inlined call is replaced: a tail call continues in the callee's
    body, any other runs the body in a lambda invoked in its place. *)
type inlined_as =
  | Continued
  | Invoked

(** Parameters for a single inlining substitution. *)
type inline_spec = {
  continues : cpp_expr -> bool;
      (** [true] if [expr], returned, is a call that continues in the body of
          the function being inlined *)
  invokes : cpp_expr -> bool;
      (** [true] if [expr] is a call that runs that body in its place *)
  inlined : inlined_as -> cpp_expr -> unit;
      (** Told of each call inlined, as it is replaced *)
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

(** Whether every path through [stmts] ends in a return or a throw. *)
let rec leaves stmts =
  match List.rev stmts with
  | (Sreturn _ | Sthrow _) :: _ -> true
  | Sif (_, t, e) :: _ -> leaves t && leaves e
  | Scustom_case (_, _, _, branches, _) :: _ ->
    branches <> [] && List.for_all (fun (_, _, b) -> leaves b) branches
  | Smatch (_, branches, Some default) :: _ ->
    leaves default && List.for_all (fun br -> leaves br.smb_body) branches
  | Sblock ss :: _ -> leaves ss
  | _ -> false

(** Inline all calls matching [spec] in a statement list.  Tail calls are
    expanded to parameter bindings plus body; non-tail calls become IIFEs.
    {!generic_inline_stmt} handles individual statements. *)
let rec generic_inline_stmts spec = function
  (* A tail call of a function returning nothing is its statement and a
     return.  It continues in a body every path of which ends in a return
     or a throw, as such a function's body is generated: nothing may follow
     a call the transforms read as the function's last. *)
  | Sexpr e :: Sreturn None :: _ when spec.continues e && leaves spec.body -> generic_continue spec e
  | s :: rest -> generic_inline_stmt spec s @ generic_inline_stmts spec rest
  | [] -> []

(** The tail call [e], continued in the body inlined: its parameters bound to
    its arguments, then the body. *)
and generic_continue spec e =
  spec.inlined Continued e;
  List.map2 (fun (pid, ty) arg -> Sasgn (pid, Declare (ty, None), arg)) spec.params (spec.get_args e)
  @ spec.body

(** Inline all calls matching [spec] in a single statement. *)
and generic_inline_stmt spec = function
  | Sreturn (Some e) when spec.continues e -> generic_continue spec e
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
  if spec.invokes expr then
    let () = spec.inlined Invoked expr in
    (* Non-tail call — wrap inlined body in immediately-invoked lambda, which
       is still the Core call it replaces. *)
    let lparams =
      List.map (fun (pid, ty) -> (ty, Some pid)) spec.params
    in
    let occurrence = match expr with CPPfun_call (cs, _, _) -> cs.cs_occurrence | _ -> None in
    CPPfun_call
      ( {call_opaque with cs_occurrence = occurrence},
        CPPlambda
          { cl_params = of_reversed lparams;
            cl_tparams = [];
            cl_fixpoint = None;
            cl_moved = [];
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

(** [check], narrowed to the calls the tail loop of [loop] jumps at, as its
    ControlIR has them ({!Lower_control.loop}): a call made of one of its
    Continues.  [check] still reads the call's arguments and receiver. *)
let planned_jumps loop check =
  match Option.bind loop Lower_control.loop with
  | None -> check
  | Some t ->
    let continues = Control_ir.continues t in
    fun e ->
      match made_of e with
      | Some o when List.exists (Miniml.Occurrence.equal o) continues -> check e
      | Some _ | None -> None

(** [transform jumped], the loop [loop] the transform makes, telling
    [jumped] each call it rewrites into a jump, or, tail modulo cons, builds
    a branch's cells around.  Under [CRANE_CHECK_IR] those calls must be the
    [Continue]s and [Continue_into]s of the loop's ControlIR
    ({!Lower_control.loop}), which every such loop has. *)
let checked_tail_loop loop transform =
  let jumps = ref [] in
  let body = transform (fun e -> jumps := made_of e :: !jumps) in
  ( match loop with
  | Some l when Probe.checking () -> (
    let what () =
      match l with
      | Control_ir.Loop.Function r -> Pp.str (Table.kername_of_global r)
      | Control_ir.Loop.Member _ -> Pp.str "a local fixpoint"
    in
    match Lower_control.loop l with
    | None -> Probe.violation "control IR" Pp.(str "no ControlIR for the loop of " ++ what ())
    | Some t when not (made_as_planned (Control_ir.continues t) (List.rev !jumps)) ->
      Probe.violation "control IR"
        Pp.(str "the calls the loop of " ++ what () ++ str " jumps at are not its Continues")
    | Some _ -> () )
  | Some _ | None -> () );
  body

(** [transform entered], the machine with a stack of [loop] the frame
    transform makes, telling [entered] each call it enters the machine by and
    whether it resumes after it.  Under [CRANE_CHECK_IR] those calls must be
    the [Continue]s of the loop's ControlIR ({!Lower_control.loop}), and, where
    it builds nothing tail modulo cons, those resumed after the [Continue]s
    in a [Resume]'s value.  A call is entered from every branch a
    continuation is merged into, so they are compared as sets.  A machine
    leaving a call [check] recognises is not one: its decline is reported
    with the outcome ({!report_outcome}). *)
let checked_frame_machine loop check transform =
  let entries = ref [] in
  let body = transform (fun ~resumes e -> entries := (resumes, made_of e) :: !entries) in
  ( match loop with
  | Some l when Probe.checking () && classify check body = No_recursion -> (
    let what () =
      match l with
      | Control_ir.Loop.Function r -> Pp.str (Table.kername_of_global r)
      | Control_ir.Loop.Member _ -> Pp.str "a local fixpoint"
    in
    let within a b = List.for_all (fun o -> List.exists (Miniml.Occurrence.equal o) b) a in
    let same a b = within a b && within b a in
    let made resumed = List.filter_map (fun (r, o) -> if resumed r then o else None) !entries in
    match Lower_control.loop l with
    | None -> Probe.violation "control IR" Pp.(str "no ControlIR for the machine of " ++ what ())
    | Some _ when List.exists (fun (_, o) -> not (Option.has_some o)) !entries ->
      Probe.violation "control IR"
        Pp.(str "the machine of " ++ what () ++ str " is entered by a call made of no Core call")
    | Some t ->
      if not (same (made (fun _ -> true)) (Control_ir.continues t)) then
        Probe.violation "control IR"
          Pp.(str "the calls the machine of " ++ what () ++ str " is entered by are not its Continues");
      if Control_ir.continues_into t = [] && not (same (made Fun.id) (Control_ir.resumed t)) then
        Probe.violation "control IR"
          Pp.(str "the calls the machine of " ++ what () ++ str " resumes after are not its Resumes' Continues") )
  | Some _ | None -> () );
  body

(** The name a local of a body inlined into another takes there: prefixed,
    so that it collides with none of the other body's, and a temporary
    still where it was one ({!Mlutil.is_temporary_id}), so that
    {!Cpp_temporaries} puts it back where it is read. *)
let inlined_local_name id =
  if Mlutil.is_temporary_id id then Id.of_string (Id.to_string id ^ "_inl")
  else Generated_name.prefixed "_inl" id

(** [inline_partner ~continues ~invokes callee body] is [body] with the
    calls [continues] and [invokes] recognise replaced by the body of
    [callee], registered in {!mutual_fn_table}: a returned call that
    continues in it by parameter bindings and the body, any other by a
    lambda invoked in its place, which is still the Core call it replaces.
    With it come the occurrences of the calls replaced so, those that
    continued and those invoked.

    Parameter names in the inlined body are prefixed with [_inl_] to avoid
    collisions with the outer function's variables, and so are its locals. *)
let inline_partner ~continues ~invokes
    {rf_ret_ty = callee_ret_ty; rf_params = callee_params; rf_body = callee_body} body =
  (* Generate fresh names for parameters AND all local variables to avoid
     collision with the outer function's bindings. *)
  let param_rename_map =
    List.map
      (fun (pid, _ty) -> (pid, Generated_name.prefixed "_inl" pid))
      callee_params
  in
  let local_ids = declared_ids callee_body in
  let local_rename_map =
    List.filter_map (fun id ->
      if List.mem_assoc id param_rename_map then None
      else Some (id, inlined_local_name id))
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
  let rename_var id =
    match List.assoc_opt id rename_map with
    | Some fresh -> fresh
    | None -> id
  in
  let get_call_args = function
    | CPPfun_call (_, _, args) -> to_reversed args
    | _ -> []
  in
  let continued = ref [] and invoked = ref [] in
  let inlined how e =
    match how with
    | Continued -> continued := made_of e :: !continued
    | Invoked -> invoked := made_of e :: !invoked
  in
  let body =
    generic_inline_stmts
      { continues;
        invokes;
        inlined;
        get_args = get_call_args;
        params = fresh_params;
        body = rename_ids rename_var callee_body;
        ret_ty = callee_ret_ty }
      body
  in
  (body, List.rev !continued, List.rev !invoked)

(** Inline mutual recursion partners into the body of the function [r] as
    the recursion plan has them ({!Recursion_plan.inlinings}): each partner
    as [partner] has it -- registered in {!mutual_fn_table}, unless given --
    at the calls whose occurrences the plan lists, a tail call continuing in
    the partner's body and any other running it in a lambda invoked in
    place.  The function then calls itself where it called them, and can be
    loopified by {!transform_fundef}.

    Under [CRANE_CHECK_IR] the calls inlined must be those planned. *)
let try_inline_mutual_into ?(partner = Ref.User.Tbl.find_opt mutual_fn_table) r body =
  let planned = Recursion_plan.inlinings r in
  let made = ref [] in
  let inline_one body (i : Recursion_plan.inlining) =
    match partner i.partner with
    | None -> body
    | Some registered ->
      let call_in occurrences = function
        | CPPfun_call ({cs_occurrence = Some o; _}, CPPglob (g, _, _), _) ->
          Common.globref_equal g i.partner && List.exists (Miniml.Occurrence.equal o) occurrences
        | _ -> false
      in
      let body, continued, invoked =
        inline_partner ~continues:(call_in i.continued) ~invokes:(call_in i.invoked) registered body
      in
      made := (i.partner, continued, invoked) :: !made;
      body
  in
  let inlined = List.fold_left inline_one body planned in
  if Probe.checking () then begin
    let same_calls = made_as_planned in
    let agree hops =
      List.length planned = List.length hops
      && List.for_all2
           (fun (i : Recursion_plan.inlining) (g, continued, invoked) ->
             Common.globref_equal i.partner g && same_calls i.continued continued
             && same_calls i.invoked invoked )
           planned hops
    in
    let what () = Pp.str (Table.kername_of_global r) in
    if not (agree (List.rev !made)) then
      Probe.violation "partner inlining plan"
        Pp.(str "the calls of its partners inlined into " ++ what () ++ str " are not those planned")
  end;
  inlined

(** The strategy for a body {!classify} reads as recursing so, where no plan
    says: a loop for tail recursion, an explicit stack for any other. *)
let classified_strategy = function
  | No_recursion -> Recursion_plan.No_loop
  | Tail_recursion -> Tail_loop
  | Nontail_recursion -> Frame_stack

(** The strategy of the local fixpoint [fixpoint], whose body is [body], as
    planned for the Core fixpoint it lowers ({!Recursion_plan.strategy_at}).
    A body with no fixpoint recorded on it, or one the plan does not know, is
    classified here, which is a violation. *)
let planned_local_strategy fixpoint check body =
  let classified () = classify_in_flow check body in
  match fixpoint with
  | Some {lf_member; lf_binder; _} -> (
    let what () = Pp.(str "the local fixpoint " ++ Id.print lf_binder) in
    match Recursion_plan.strategy_at ~pointer_fields:constructor_pointer_fields lf_member with
    | Some planned -> planned
    | None ->
      Probe.violation "recursion plan" Pp.(str "the recursion plan does not know " ++ what ());
      classified_strategy (classified ()) )
  | None ->
    Probe.violation "recursion plan"
      (Pp.str "a local fixpoint's body was reached with no Core fixpoint recorded on it");
    classified_strategy (classified ())

(** The calls the machine of the function [r] is entered by, as the
    recursion plan names what a point resumes after: its own. *)
let entered_by_function r (c : Recursion_plan.call) =
  match c.target with
  | Function g -> Common.globref_equal g r
  | Member _ | Entering _ -> false

(** The calls the machine of the function [member] of a local fixpoint is
    entered by: that member's. *)
let entered_by_member (occurrence, member) (c : Recursion_plan.call) =
  match c.target with
  | Member (o, m) -> Miniml.Occurrence.equal o occurrence && Int.equal m member
  | Function _ | Entering _ -> false

(** {2 Inner lambda loopification}

    Transforms the local fixpoints within function bodies into iterative
    versions using the same while-loop or stack-frame techniques as
    top-level functions. *)

(** Walk through a statement list and loopify each local fixpoint: the
    implementation lambda of the Y-combinator pair a local [fix] becomes
    ({!Translation.gen_local_fix_by_ref}), which recurses through its
    self-parameter, as the program's recursion plan has it
    ({!planned_local_strategy}).  A [let]-bound lambda cannot name the
    variable it is bound to, so no other lambda recurses.

    Descends into all nested statement structures (if/else, while loops,
    match branches, switch, blocks) and into lambda expressions within
    assignments and returns, to find local fixpoints at any depth.

    @param tparams  Type parameters of the enclosing function
    @param body     The statement list to scan and transform
    @return The statement list with all recursive local fixpoints loopified *)
let loopify_inner_lambdas ?(tail_only = false) ~tparams ?(outer_env = []) body =
  (* What the enclosing scope binds, which a local fixpoint captures. *)
  let outer_env = collect_type_env body @ outer_env in
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
     recursion, reuse {!transform_tail} with a checker taking the calls the
     recursion plan finds of the member ({!planned_self_checker}), dropping
     the trailing self-forward argument so the remaining args align
     positionally with the non-self loop params.  After transformation the
     self-parameter is unreferenced; the {!Cpp_print} lambda printer emits
     unreferenced params without a name, so there is no [-Wunused-parameter].
     Only single (non-mutual) fixpoints are handled; mutual ones (multiple
     self-params) and non-tail recursion are left unchanged. *)
  let try_loopify_ycomb ~fixpoint lparams ret_ty_opt lbody =
    match (fixpoint, fixpoint_self fixpoint lparams) with
    | None, _ | _, None -> None
    | Some {lf_name; lf_binders; lf_member; _}, Some self_id -> (
      let check = planned_self_checker lf_member in
      let lbody = expose_tail_calls check lbody in
      match planned_local_strategy fixpoint check lbody with
      | No_loop -> None
      (* A local cofixpoint: its calls run when a thunk is forced, after it
         has returned, as a top-level one's do ({!transform_fundef_exn}). *)
      | Suspended _ -> None
      | (Modulo_cons _ | Frame_stack) when tail_only -> None
      | (Tail_loop | Modulo_cons _ | Frame_stack) as strategy ->
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
        (* The frame structs a non-tail transform emits are named after the
           fixpoint. *)
        let name = Id.to_string lf_name in
        let body' =
          match strategy with
          | Tail_loop ->
            report_outcome ~name ~check ~strategy:Lp_tail
              (let loop = Some (Control_ir.Loop.Member (fst lf_member, snd lf_member)) in
               checked_tail_loop loop (fun jumped ->
                   transform_tail ~jumped tparams (planned_jumps loop check) params ret_ty lbody ) )
          (* The tail-modulo-cons loop is built for a function, not a lambda:
             a local fixpoint gets it only through a helper lifted out of it. *)
          | Modulo_cons _ | Frame_stack ->
            report_outcome ~name ~check ~strategy:Lp_frame
              (transform_nontail ~fn_name:name ~outer_env ~binders:lf_binders
                 ~entered_by:(entered_by_member lf_member) check tparams
                 params ret_ty lbody)
          | No_loop | Suspended _ ->
            CErrors.anomaly (Pp.str "loopify: no loop cannot appear here")
        in
        (* A call the transform left -- one in a closure, say a fixpoint in
           the body that calls back, which a local machine does not adopt --
           recurses through the self-parameter the loop drops, so the
           fixpoint is left as it was: the decline {!report_outcome}
           recorded.  Params the loop body no longer mentions keep their
           names here; the lambda printer drops the name of any param its
           body does not reference, so unused ones do not trip
           [-Wunused-parameter]. *)
        if classify check body' = No_recursion then Some (lparams, body') else None )
  in
  let rec process_stmts stmts =
    match stmts with
    | [] -> []
    (* A Y-combinator local fixpoint from {!gen_local_fix_by_ref}:
       [Sasgn(id, Declare Tauto, CPPlambda(...))] whose last param is the
       single self-reference its encoding recorded. *)
    | Sasgn
        ( id,
          (Declare (Tauto, _) as tgt),
          CPPlambda
            { cl_params = lparams;
              cl_ret = ret_ty_opt;
              cl_body = lbody;
              cl_capture = cap;
              cl_fixpoint = fixpoint;
              cl_moved = moved;
              _ } )
      :: rest
      when Option.has_some (fixpoint_self fixpoint (to_reversed lparams)) ->
      (* The loop is made where the impl was, or just after it where the
         wrapper was, nothing reading in between: it takes by move what the
         impl took that it still captures. *)
      let keep_moves l =
        CPPlambda {l with cl_moved = List.filter (fun x -> List.mem x (free_vars_expr (CPPlambda l))) moved}
      in
      ( match try_loopify_ycomb ~fixpoint (to_reversed lparams) ret_ty_opt lbody with
      | Some (lparams', lbody') -> (
        (* The loop no longer recurses, so the self-parameter and the wrapper
           that supplied it are scaffolding: the wrapper [go] becomes the loop
           itself, an ordinary lambda.  Only when the next statement is that
           wrapper ({!wraps}) and nothing after it names [go_impl].  The local
           fixpoints in the loop are lowered too, as in any other body. *)
        let self = fixpoint_self fixpoint (to_reversed lparams) in
        let lbody' = process_stmts lbody' in
        match rest with
        | Sasgn (wid, (Declare (Tauto, _) as wtgt), CPPlambda w) :: rest'
          when wraps fixpoint w && not (List.exists (Id.equal id) (free_vars_body rest')) ->
          Sasgn
            ( wid,
              wtgt,
              keep_moves
                { cl_params =
                    of_reversed
                      (List.filter (fun (_, x) -> x <> self) lparams');
                  cl_tparams = [];
                  cl_fixpoint = Option.map (fun f -> {f with lf_encoding = Lowered}) fixpoint;
                  cl_moved = [];
                  cl_ret = ret_ty_opt;
                  cl_body = lbody';
                  cl_capture = cap } )
          :: process_stmts rest'
        | _ ->
          Sasgn
            (id, tgt, keep_moves
              { cl_params = of_reversed lparams';
              cl_tparams = [];
              cl_fixpoint = fixpoint;
              cl_moved = [];
                cl_ret = ret_ty_opt;
                cl_body = lbody';
                cl_capture = cap })
          :: process_stmts rest )
      | None ->
        let lbody' = process_stmts lbody in
        Sasgn (id, tgt, keep_moves
          { cl_params = lparams;
          cl_tparams = [];
          cl_fixpoint = fixpoint;
          cl_moved = [];
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

(** {2:cofixpoints Cofixpoints}

    Cofixpoints (corecursive definitions) returning a standard coinductive type
    are suspended: wrapped in a [lazy_] thunk whole, or at the constructors
    whose arguments may run the corecursion.  This defers evaluation so the
    infinite corecursive structure is built on demand rather than eagerly.
    The recursion plan says which functions these are, before any is lowered
    ({!Recursion_plan.Suspended}).

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
    so that any local fixpoints nested inside the thunk are
    loopified independently. *)

(** Apply nontail-recursion loopification, trying strategies in priority order:
    {ol
      {- {b Branch dependency} — bail out if any return expression depends on a
         destructured match binding that is also passed to a recursive call
         (the frame-based rewriter can't handle this yet).}
      {- {b TMC} ({!transform_tmc}) — if the recursion plan lowers it "tail
         modulo cons" (each non-tail call the one call of a constructor
         chain), each return read as one of the plan's chains
         ({!branch_along}).}
      {- {b General nontail} ({!transform_nontail}) — frame-based stack for all
         other patterns, including multi-call (e.g. fibonacci, tree traversal).}}

    @param param_inits Optional custom initialisers for shadow / [_self]
                       variables. Forwarded to {!transform_tmc} and
                       {!transform_nontail} so that method receivers can be
                       initialised directly from [this].
    @param fn_name     Optional function name for loop-comment annotations
                       (forwarded to {!transform_nontail}).
    @param loop        The loop the transform makes, whose ControlIR it must
                       agree with ({!checked_tail_loop},
                       {!checked_frame_machine})
    @param modulo_cons The chains the recursion is lowered tail modulo cons
                       around, where it is so planned ({!planned_strategy})
    @param check       Call checker for identifying recursive calls
    @param tparams     Template parameter context
    @param adopted     A body calling back into this function, to adopt as a
                       second machine entry; see {!transform_nontail}
    @param params      Function parameters [(id, type)]
    @param ret_ty      Return type
    @param body        Function body statements
    @return what the transform did; see {!nontail_result}. *)
let apply_nontail_loopification ?(param_inits = []) ?fn_name ?adopted ?entered_by ?modulo_cons ?loop
    ?binders check tparams params ret_ty body =
  let declined reason =
    {nt_body = body; nt_outcome = Lp_declined reason; nt_used_param_inits = false}
  in
  if has_recursive_branch_dependency check body then
    declined "recursive call in a branch condition or dispatch scrutinee"
  else
  let frame () =
    (* An adopted body enters the machine by calls of its own, which the
       loop's ControlIR does not hold. *)
    let loop = if Option.has_some adopted then None else loop in
    { nt_body =
        checked_frame_machine loop check (fun entered ->
            transform_nontail ?fn_name ?adopted ?entered_by ~entered ?binders check tparams params ret_ty body );
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
  (* The loop, where the plan lowers the function tail modulo cons: every
     call that is not a tail call is the one call of one of its chains
     ({!Recursion_plan.Modulo_cons}), so the transform, which rewrites calls
     directly under a constructor, leaves none behind -- a body mixing a
     branch that conses onto the recursive result with one that scrutinises
     it has no plan to be.  A self-call left behind is the finished body
     disagreeing with the plan, a violation under [CRANE_CHECK_IR]; the
     function falls back to the frame stack. *)
  let tmc =
    match modulo_cons with
    | Some chains ->
      let tmc =
        checked_tail_loop loop (fun jumped ->
            transform_tmc ~param_inits ~jumped ~shapes:(chain_shapes chains) tparams check params ret_ty restored )
      in
      if classify check tmc = No_recursion then Some tmc
      else (
        Probe.violation "tail modulo cons plan"
          (Pp.str "a self-call survived the transform the recursion plan's chains describe");
        None )
    | None -> None
  in
  match tmc with
  | Some tmc -> {nt_body = tmc; nt_outcome = Lp_tmc; nt_used_param_inits = true}
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
      Ref.User.Tbl.find_opt mutual_fn_table r
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
        let keep_params =
          List.filteri (fun i _ -> i <> k) g_params
        in
        let rename_map =
          List.map
            (fun id -> (id, inlined_local_name id))
            (List.map fst keep_params @ declared_ids g_body)
        in
        let rename_var id =
          match List.assoc_opt id rename_map with Some f -> f | None -> id
        in
        let fresh_params =
          List.map (fun (pid, ty) -> (rename_var pid, ty)) keep_params
        in
        let fresh_body = rename_ids rename_var g_body in
        (* Match exactly the knot call: a call to a registered functional whose
           argument at position [k] is the eta-self lambda. *)
        let knot_call = function
          | CPPfun_call (_, callee, cargs) ->
            let cargs = to_reversed cargs in
            lookup_functional callee <> None
            && List.length cargs = List.length args
            && (match List.nth_opt cargs k with
               | Some a -> eta_self_head a <> None
               | None -> false)
          | _ -> false
        in
        let spec =
          {
            continues = knot_call;
            invokes = knot_call;
            inlined = (fun _ _ -> ());
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

(** The loop a tail loop of the function [r] is: a local fixpoint's member,
    for a helper lifted for one; none for one lifted for a lambda. *)
let function_loop r =
  match Option.map Lifted.site (Lifted.of_ref r) with
  | Some (Fixpoint (occurrence, member)) -> Some (Control_ir.Loop.Member (occurrence, member))
  | Some (Let _) -> None
  | None -> Some (Control_ir.Loop.Function r)

(** The strategy of the function [r], whose body is [body]: as the
    program's recursion plan has it ({!Recursion_plan.strategy}), read off its
    Core body and its recursive group's before any of them was lowered, given
    the constructor fields planned behind the pointer.  A helper lifted out of
    a definition for one of its local fixpoints is planned by that fixpoint,
    and one lifted for a lambda a let binds by that let.

    A function the plan does not know is classified here, from [body], the
    finished body, which is a violation.  A member the backend generates
    itself -- a factory, a deep copy -- has no Core body and no reference,
    and is classified here. *)
let planned_strategy r check body =
  let classified () = classify_in_flow check body in
  match r with
  | None -> classified_strategy (classified ())
  | Some r -> (
    let pointer_fields = constructor_pointer_fields in
    let planned =
      match Option.map Lifted.site (Lifted.of_ref r) with
      | Some (Fixpoint (occurrence, member)) -> Recursion_plan.strategy_at ~pointer_fields (occurrence, member)
      | Some (Let occurrence) -> Recursion_plan.strategy_of_let occurrence
      | None -> Recursion_plan.strategy ~pointer_fields r
    in
    let what () = Pp.str (Table.kername_of_global r) in
    match planned with
    | Some planned -> planned
    | None ->
      Probe.violation "recursion plan" Pp.(str "the recursion plan does not know " ++ what ());
      classified_strategy (classified ()) )

(** The local fixpoints the machine of [r] may adopt, as the recursion plan
    has them ({!Recursion_plan.adoptable}): a helper lifted for a local
    fixpoint's function is planned by it. *)
let planned_adoptable r =
  match Lifted.of_ref r with
  | Some h -> (
    match Lifted.fixpoint h with Some m -> Recursion_plan.adoptable_at m | None -> [] )
  | None -> Recursion_plan.adoptable r

(** The chains a strategy lowers tail modulo cons around, if it does. *)
let modulo_cons_chains = function
  | Recursion_plan.Modulo_cons chains -> Some chains
  | No_loop | Tail_loop | Frame_stack | Suspended _ -> None

let checker_tail_loop ~partner ~tparams (f : dfun) params body =
  let r = fst f.df_path.dp_outer in
  let check = fn_checker (dfun_path_list f.df_path) in
  let body = expose_tail_calls check (try_inline_mutual_into ~partner r body) in
  transform_tail tparams (planned_jumps (function_loop r) check) params f.df_ret body

let after_tail_loop ?(strategy = Lp_tail) ~tparams (f : dfun) params loop =
  report_outcome ~name:(fundef_display_name f.df_path) ~check:(fn_checker (dfun_path_list f.df_path))
    ~strategy
    (loopify_inner_lambdas ~tparams ~outer_env:params loop)

let checker_modulo_cons ~partner ~tparams (f : dfun) params body =
  let r = fst f.df_path.dp_outer in
  let check = fn_checker (dfun_path_list f.df_path) in
  let body = expose_tail_calls check (try_inline_mutual_into ~partner r body) in
  match planned_strategy (Some r) check body with
  | Modulo_cons chains -> (apply_nontail_loopification ~modulo_cons:chains check tparams params f.df_ret body).nt_body
  | No_loop | Tail_loop | Frame_stack | Suspended _ -> body

let modulo_cons_loop ~jumped ~varying ~shapes ~tparams check (f : dfun) params body =
  let names = dfun_path_list f.df_path in
  let r = fst f.df_path.dp_outer in
  let adopted () =
    find_adopted ~adoptable:(planned_adoptable r) ~invocations:(Recursion_plan.adopted_invocations r) body
  in
  if try_inline_functional_into names body != body || Option.has_some (adopted ())
     || has_recursive_branch_dependency check body
  then None
  else
    let loop =
      transform_tmc ~jumped ~varying ~shapes tparams check params f.df_ret (Cpp_temporaries.own_stmts body)
    in
    if classify (fn_checker names) loop = No_recursion then Some loop else None

let lower_local_tail_loops ~tparams stmts = loopify_inner_lambdas ~tail_only:true ~tparams stmts

let check_lowered decl =
  let rec check = function
    | Dtemplate (_, _, d) -> check d
    | Dfun ({df_loop = Some _; df_shape = Ddef (_, body); _} as f)
      when try_inline_functional_into (dfun_path_list f.df_path) body != body ->
      Probe.violation "control lowering"
        Pp.(
          str "the tail loop of " ++ str (Table.kername_of_global (fst f.df_path.dp_outer))
          ++ str ", lowered from its ControlIR, ties the knot of a functional Loopify inlines" )
    | _ -> ()
  in
  check decl

(** Transform a top-level function definition by loopifying its body.

    This is the main entry point for loopifying a [Dfun]. The transformation
    proceeds in three steps, reading {!mutual_fn_table}, where every function
    of the unit was registered before any was finished:

    + Try to inline mutual recursion partners via {!try_inline_mutual_into},
      converting mutual recursion into self-recursion.
    + Classify the recursion pattern with {!classify} and apply the appropriate
      strategy: {!transform_tail} for tail recursion, or {!transform_nontail}
      for the general case (including multi-call patterns).
    + Post-pass with {!loopify_inner_lambdas} to loopify any local
      fixpoints nested within the body.

    A cofixpoint returning a coinductive type is suspended: its recursive
    calls are captured inside closures and never executed at call time, so
    the function returns in O(1) stack frames and loopification is
    unnecessary.  The plan says so ({!Recursion_plan.Suspended}) and the
    main loopification pass is skipped; see the {!section-cofixpoints}
    section for the full rationale.

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
  (* Try to inline mutual recursion partners, every function of the unit
     registered before any was finished ({!register_decl}). *)
  let body = try_inline_mutual_into (fst f.df_path.dp_outer) body in
  (* What the machine is entered by in the plan's terms: the function's
     calls, or a lifted helper's local fixpoint member's.  A partner inlined
     into it leaves no call of its own: a tail call continues in its body,
     whose statements the plan has resume points for as the partner's, and
     any other is an invocation, entering the machine only if adopted. *)
  let entered_by =
    let r = fst f.df_path.dp_outer in
    match Lifted.of_ref r with
    | Some h -> Option.map entered_by_member (Lifted.fixpoint h)
    | None -> Some (entered_by_function r)
  in
  (* Inline an Equations-style functional applied to itself so its hidden
     recursion becomes ordinary self-recursion that loopifies. *)
  let body = try_inline_functional_into names body in
  let check = fn_checker names in
  let body = expose_tail_calls check body in
  (* A suspended cofixpoint's calls are captured inside closures and never
     executed at call time -- the function returns a thunk in O(1) stack
     frames.  Loopification is unnecessary and TMC would generate invalid
     [v_mut()] calls (see {!section-cofixpoints}).  We still run
     [loopify_inner_lambdas] to handle any local fixpoints nested inside the
     thunk. *)
  let body =
    let name = fundef_display_name f.df_path in
    let strategy = planned_strategy (Some (fst f.df_path.dp_outer)) check body in
    match strategy with
    | Suspended _ ->
      record_outcome name (Lp_deferred "cofixpoint body is lazy_-wrapped");
      loopify_inner_lambdas ~tparams ~outer_env:params body
    | No_loop | Tail_loop | Modulo_cons _ | Frame_stack ->
      (* Recursion that lives inside a lambda -- a local fixpoint, or an
         inlined mutual partner -- is visible to {!classify} but out of reach
         of the transforms, which never rewrite through a lambda: the machine
         they emit for it pushes nothing and its loop runs once.  Note the
         body now, while it still has the shape the search recognises, so the
         decline names it instead of reporting the generic "a self-call
         survived". *)
      let adopted =
        match strategy with
        | Modulo_cons _ | Frame_stack ->
          find_adopted ~adoptable:(planned_adoptable (fst f.df_path.dp_outer))
            ~invocations:(Recursion_plan.adopted_invocations (fst f.df_path.dp_outer))
            body
        | No_loop | Tail_loop | Suspended _ -> None
      in
      let survived = Option.map decline_reason adopted in
      let body, outcome =
        match strategy with
        | No_loop | Suspended _ -> (body, None)
        | Tail_loop ->
          ( (let loop = function_loop (fst f.df_path.dp_outer) in
             checked_tail_loop loop (fun jumped ->
                 transform_tail ~jumped tparams (planned_jumps loop check) params ret_ty body ) ),
            Some Lp_tail )
        | Modulo_cons _ | Frame_stack ->
          let r =
            apply_nontail_loopification ~fn_name:name ?adopted ?entered_by ~binders:f.df_binders
              ?loop:(function_loop (fst f.df_path.dp_outer))
              ?modulo_cons:(modulo_cons_chains strategy)
              check tparams params ret_ty body
          in
          (r.nt_body, Some r.nt_outcome)
      in
      (* A self-call can sit inside an inner lambda, where the transforms above
         deliberately leave it alone; [loopify_inner_lambdas] is what removes
         it.  Judge the postcondition only once that has run, or every such
         function is reported as declined even though the emitted code holds no
         self-call. *)
      let body = loopify_inner_lambdas ~tparams ~outer_env:params body in
      (match outcome with
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
    linearise never aborts the surrounding extraction.  A function whose loop
    was lowered as it was generated ({!Control_to_legacy_minicpp}) is left
    as it is. *)
let transform_fundef ~tparams (f : dfun) params body =
  let qualified () =
    String.concat "::"
      (List.map
         (fun (r, _) -> Table.kername_of_global r)
         (f.df_path.dp_outer :: f.df_path.dp_inner))
  in
  if Option.has_some f.df_loop then Dfun f
  else
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
    + Creates a {!method_checker} for the global the method was made from.
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
    @param varying        Which of the receiver and the parameters a tail
                          loop varies, where the caller knows; read off its
                          calls otherwise
    @return An [Fmethod] field with the loopified body *)
let transform_method_own ?varying ~tparams ~self_ty mf =
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
  let name = Id.to_string mf.mf_name in
  let basic_check =
    method_checker ~n_params ~has_self_param:false ~this_pos mf.mf_globref
  in
  let strategy = planned_strategy mf.mf_globref basic_check mf.mf_body in
    ( match strategy with
    (* A suspended method returns in O(1) stack frames, as a function does
       ({!transform_fundef_exn}). *)
    | Suspended _ ->
      record_outcome name (Lp_deferred "cofixpoint body is lazy_-wrapped");
      Fmethod mf
    | No_loop ->
      Fmethod mf
    | Tail_loop | Modulo_cons _ | Frame_stack ->
      let self_id = id_self in
      let body_with_self = List.map (this_to_self_stmt self_id) mf.mf_body in
      let self_check =
        method_checker ~n_params ~has_self_param:true ~this_pos mf.mf_globref
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
        let is_self r =
          match mf.mf_globref with Some sr -> Common.globref_equal r sr | None -> false
        in
        let park e =
          match e with
          | CPPfun_call (cs, CPPglob (r, targs, x), args)
            when is_self r && List.length (to_reversed args) > n_params ->
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
              Some (recv, CPPfun_call (cs, CPPglob (r, targs, x), of_reversed args'))
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
        match (strategy, self_store_ty) with
        | (Tail_loop, Some _) -> park_value_receivers body_with_self
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
        match strategy with
        | Tail_loop ->
          ( report_outcome ~name ~check:self_check ~strategy:Lp_tail
              (let loop = Option.bind mf.mf_globref function_loop in
               checked_tail_loop loop (fun jumped ->
                   transform_tail ~param_inits:[(self_id, CPPthis)] ~jumped ?varying tparams
                     (planned_jumps loop self_check) augmented_params mf.mf_ret_type body_with_self ) ),
            false )
        | Modulo_cons _ | Frame_stack ->
          let fn_name = Some name in
          let r =
            apply_nontail_loopification
              ?entered_by:(Option.map entered_by_function mf.mf_globref)
              ~param_inits:[(self_id, CPPthis)]
              ~binders:
                ( (match mf.mf_receiver_binder with Some b -> [(self_id, b)] | None -> [])
                @ mf.mf_binders )
              ?fn_name ?modulo_cons:(modulo_cons_chains strategy)
              ?loop:(Option.bind mf.mf_globref function_loop)
              self_check tparams
              augmented_params mf.mf_ret_type body_with_self
          in
          let body' =
            report_outcome ~name ~check:self_check ~strategy:r.nt_outcome
              r.nt_body
          in
          (body', not r.nt_used_param_inits)
        | No_loop | Suspended _ -> CErrors.anomaly (Pp.str "loopify: no loop cannot appear here")
      in
      (* Declare the parking slot outside the loop so the pointer taken to it
         on the back-edge stays valid for the next iteration. *)
      let body' =
        match self_store_ty with
        | Some ty -> Sdecl (id_self_store, ty, None) :: body'
        | None -> body'
      in
      if needs_init_self then
        let init_self = Sasgn (self_id, Declare (self_ty, None), CPPthis) in
        Fmethod {mf with mf_body = init_self :: body'}
      else
        Fmethod {mf with mf_body = body'} )

(** {!transform_method_own}, then the tail-recursive local fixpoints in the
    method's body turned into loops: the part of loopification every
    declaration gets ({!transform_local_tail_loops}), which a method of a
    struct whose methods are loopified did not. *)
let transform_method ~tparams ~self_ty mf =
  match transform_method_own ~tparams ~self_ty mf with
  | Fmethod m ->
    Fmethod
      { m with
        mf_body =
          loopify_inner_lambdas ~tail_only:true ~tparams:(tparams @ mf.mf_tparams) ~outer_env:mf.mf_params
            m.mf_body }
  | f -> f

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
  (* A method lowered from its ControlIR as it was generated
     ({!Control_to_legacy_minicpp}). *)
  | Fmethod {mf_loop = Some _; _} -> (fld, vis, tag)
  | Fmethod mf
    when (match mf.mf_globref with Some r -> Table.loopifies_method r | None -> true) ->
    (transform_method ~tparams ~self_ty mf, vis, tag)
  | Fnested_struct (id, fields) ->
    let fields' =
      List.map (transform_field ~tparams ~self_ty) fields
    in
    (Fnested_struct (id, fields'), vis, tag)
  | _ -> (fld, vis, tag)

(** [transform_local_tail_loops decl] turns the tail-recursive local
    fixpoints in [decl]'s bodies into loops, and leaves everything else as it
    was.  A tail loop needs no frame and changes no evaluation order, so it is
    the part of loopification every declaration gets, whatever
    {!Cpp_pipeline.should_loopify} says about the rest. *)
let rec transform_local_tail_loops ?(tparams = []) decl =
  let body ps b = loopify_inner_lambdas ~tail_only:true ~tparams ~outer_env:ps b in
  let rec field (f, vis, tag) =
    let f =
      match f with
      | Fmethod m -> Fmethod {m with mf_body = body m.mf_params m.mf_body}
      | Fnested_struct (id, fs) -> Fnested_struct (id, List.map field fs)
      | f -> f
    in
    (f, vis, tag)
  in
  match decl with
  | Dtemplate (tparams, c, inner) ->
    Dtemplate (tparams, c, transform_local_tail_loops ~tparams inner)
  | Dfun ({df_shape = Ddef (ps, b); _} as f) ->
    Dfun {f with df_shape = Ddef (ps, body ps b)}
  | Dstruct ds -> Dstruct {ds with ds_fields = List.map field ds.ds_fields}
  | Dfields ds -> Dfields {ds with ds_fields = List.map field ds.ds_fields}
  | Dnspace (r, ds) -> Dnspace (r, List.map (transform_local_tail_loops ~tparams) ds)
  | d -> d

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
    let fields = ds.ds_fields in
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
        if ptr_fields <> [] then agree_ptr_fields ds.ds_ref ctor_name ptr_fields;
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
  | Dnspace (r, decls) -> Dnspace (r, List.map (transform_decl ~tparams) decls)
  | d -> d
