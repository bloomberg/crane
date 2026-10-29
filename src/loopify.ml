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
    between them and inlines mutual recursion.  What it lowers, and where,
    is the recursion plan's, read off the ControlIR of each loop as the
    definition is generated ({!Control_to_legacy_minicpp}).

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
  binders : (Id.t * Core_binder.t) list;
      (** The Core binder each of them stands for, by name *)
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
  List.map2
    (fun (pid, ty) arg -> Sasgn (pid, Declare (ty, List.assoc_opt pid spec.binders), arg))
    spec.params (spec.get_args e)
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
            cl_binders = spec.binders;
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

(** How the calls the machine of the loop [l] is entered by, [entries],
    each with whether it resumes after it, disagree with its ControlIR, if
    they do ({!Lower_control.loop}): they must be its [Continue]s, and,
    where it builds nothing tail modulo cons, those resumed after the
    [Continue]s in a [Resume]'s value.  A call is entered from every branch
    a continuation is merged into, so they are compared as sets. *)
let machine_disagreement l entries =
  let what () =
    match l with
    | Control_ir.Loop.Function r -> Pp.str (Table.kername_of_global r)
    | Control_ir.Loop.Member _ -> Pp.str "a local fixpoint"
  in
  let within a b = List.for_all (fun o -> List.exists (Miniml.Occurrence.equal o) b) a in
  let same a b = within a b && within b a in
  let made resumed = List.filter_map (fun (r, o) -> if resumed r then o else None) entries in
  match Lower_control.loop l with
  | None -> Some Pp.(str "no ControlIR for the machine of " ++ what ())
  | Some _ when List.exists (fun (_, o) -> not (Option.has_some o)) entries ->
    Some Pp.(str "the machine of " ++ what () ++ str " is entered by a call made of no Core call")
  | Some t ->
    if not (same (made (fun _ -> true)) (Control_ir.continues t)) then
      Some Pp.(str "the calls the machine of " ++ what () ++ str " is entered by are not its Continues")
    else if Control_ir.continues_into t = [] && not (same (made Fun.id) (Control_ir.resumed t)) then
      Some Pp.(str "the calls the machine of " ++ what () ++ str " resumes after are not its Resumes' Continues")
    else None

(** [transform entered], the machine with a stack of [loop] the frame
    transform makes, telling [entered] each call it enters the machine by and
    whether it resumes after it, with those calls; [None] where it enters it
    by none, and the machine, which would run its body once, is not made.  A
    recursion it does not take is then left where it was.  Under
    [CRANE_CHECK_IR] the calls must agree with the loop's ControlIR
    ({!machine_disagreement}).  A machine leaving a call [check] recognises
    is not judged: its decline is reported with the outcome
    ({!report_outcome}). *)
let checked_frame_machine loop check transform =
  let entries = ref [] in
  let body = transform (fun ~resumes e -> entries := (resumes, made_of e) :: !entries) in
  if !entries = [] then None
  else begin
    ( match loop with
    | Some l when Probe.checking () && classify check body = No_recursion ->
      Option.iter (Probe.violation "control IR") (machine_disagreement l !entries)
    | Some _ | None -> () );
    Some (body, !entries)
  end

(** The name a local of a body inlined into another takes there: prefixed,
    so that it collides with none of the other body's, and a temporary
    still where it was one ({!Mlutil.is_temporary_id}), so that
    {!Cpp_temporaries} puts it back where it is read. *)
let inlined_local_name id =
  if Mlutil.is_temporary_id id then Id.of_string (Id.to_string id ^ "_inl")
  else Generated_name.prefixed "_inl" id

(** [inline_partner ~continues ~invokes callee body] is [body] with the
    calls [continues] and [invokes] recognise replaced by the body of
    [callee], as it was generated: a returned call that
    continues in it by parameter bindings and the body, any other by a
    lambda invoked in its place, which is still the Core call it replaces.
    With it come the occurrences of the calls replaced so, those that
    continued and those invoked.

    Parameter names in the inlined body are prefixed with [_inl_] to avoid
    collisions with the outer function's variables, and so are its locals. *)
let inline_partner ~continues ~invokes
    {rf_ret_ty = callee_ret_ty; rf_params = callee_params; rf_binders = callee_binders; rf_body = callee_body} body =
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
        binders = List.map (fun (pid, b) -> (rename_var pid, b)) callee_binders;
        body = rename_ids rename_var callee_body;
        ret_ty = callee_ret_ty }
      body
  in
  (body, List.rev !continued, List.rev !invoked)

(** Inline mutual recursion partners into the body of the function [r] as
    the recursion plan has them ({!Recursion_plan.inlinings}): each partner
    as [partner] has it, at the calls whose occurrences the plan lists, a
    tail call continuing in the partner's body and any other running it in a
    lambda invoked in place.  The function then calls itself where it
    called them, and its loop is lowered as a function's is.

    Under [CRANE_CHECK_IR] the calls inlined must be those planned. *)
let try_inline_mutual_into ~partner r body =
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

(** The calls the machine of the definition [r] is entered by: a
    function's own, or those of the member of the local fixpoint a helper
    lifted out for it lowers. *)
let entered_by_definition r =
  match Lifted.of_ref r with
  | Some h -> Option.map entered_by_member (Lifted.fixpoint h)
  | None -> Some (entered_by_function r)

(** The recursive calls of the definition [r], each by the occurrence the
    C++ call made of it records: a function's own, in its recursive group's
    bodies ({!Recursion_plan.calls}), or those of the member of the local
    fixpoint a helper lifted for it lowers.  A call of one of them left in
    its finished body is one it still recurses by. *)
let definition_calls r =
  match Lifted.of_ref r with
  | Some h -> Option.cata Recursion_plan.member_calls [] (Lifted.fixpoint h)
  | None -> Recursion_plan.calls r

(** The calls a finished body of the function [f] still recurses by
    ({!definition_calls}), whatever C++ heads them. *)
let survivors (f : dfun) = calls_checker (List.concat_map (fun (r, _) -> definition_calls r) (dfun_path_list f.df_path))

(** {!survivors} of the method [mf]. *)
let method_survivors mf = calls_checker (Option.cata definition_calls [] mf.mf_globref)

(** {2 Inner lambda loopification}

    Transforms the local fixpoints within function bodies into iterative
    versions using the same while-loop or stack-frame techniques as
    top-level functions. *)

let kept_positions (l : Control_ir.Term.loop) =
  List.filteri (fun _ (_, ty) -> not (Ml_type_util.void_binder ty)) (List.mapi (fun i (_, ty) -> (i, ty)) l.parameters)
  |> List.rev_map fst

(** Why a local fixpoint whose ControlIR says nothing of the parameters its
    loop varies is not lowered. *)
let no_varying_plan = "no ControlIR loop says which parameters vary"

let member_varying member params =
  match Lower_control.loop (Control_ir.Loop.Member (fst member, snd member)) with
  | Some (Loop l) ->
    let kept = kept_positions l in
    if List.compare_lengths kept params <> 0 then None
    else
      let invariant = Control_ir.invariant_parameters l in
      Some (List.map (fun i -> not (List.nth invariant i)) kept)
  | Some _ | None -> None

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
let loopify_inner_lambdas ?(tail_only = false) ?parts ~tparams ?(outer_env = []) body =
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
  let try_loopify_ycomb ~fixpoint ~binders lparams ret_ty_opt lbody =
    match (fixpoint, fixpoint_self fixpoint lparams) with
    | None, _ | _, None -> None
    | Some {lf_name; lf_member; _}, Some self_id -> (
      let check = planned_self_checker lf_member in
      let lbody = expose_tail_calls check lbody in
      match planned_local_strategy fixpoint check lbody with
      | No_loop -> None
      (* A local cofixpoint: its calls run when a thunk is forced, after it
         has returned, as a top-level one's do. *)
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
        (* What every call passes each parameter, where the caller knows it
           of this fixpoint. *)
        let parts =
          match parts with
          | Some ((o, m), parts)
            when Miniml.Occurrence.equal o (fst lf_member) && Int.equal m (snd lf_member)
                 && List.compare_lengths parts params = 0 ->
            Some parts
          | Some _ | None -> None
        in
        (* The frame structs a non-tail transform emits are named after the
           fixpoint. *)
        let name = Id.to_string lf_name in
        match member_varying lf_member params with
        | None ->
          record_outcome name (Lp_declined no_varying_plan);
          None
        | Some varying ->
        let body' =
          match strategy with
          | Tail_loop ->
            report_outcome ~name ~check ~strategy:Lp_tail
              (let loop = Some (Control_ir.Loop.Member (fst lf_member, snd lf_member)) in
               checked_tail_loop loop (fun jumped ->
                   transform_tail ~jumped ~varying ?parts tparams (planned_jumps loop check) params ret_ty lbody ) )
          (* The tail-modulo-cons loop is built for a function, not a lambda:
             a local fixpoint gets it only through a helper lifted out of it. *)
          | Modulo_cons _ | Frame_stack ->
            report_outcome ~name ~check ~strategy:Lp_frame
              (transform_nontail ~fn_name:name ~loop:(Control_ir.Loop.Member (fst lf_member, snd lf_member)) ~varying ~outer_env
                 ~binders ~entered_by:(entered_by_member lf_member) ?parts check tparams
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
            ({ cl_params = lparams;
              cl_ret = ret_ty_opt;
              cl_body = lbody;
              cl_capture = cap;
              cl_fixpoint = fixpoint;
              cl_binders = binders;
              cl_moved = moved;
              _ } as l) )
      :: rest
      when Option.has_some (fixpoint_self fixpoint (to_reversed lparams)) ->
      (* The loop is made where the impl was, or just after it where the
         wrapper was, nothing reading in between: it takes by move what the
         impl took that it still captures. *)
      let keep_moves l =
        CPPlambda {l with cl_moved = List.filter (fun x -> List.mem x (free_vars_expr (CPPlambda l))) moved}
      in
      ( match try_loopify_ycomb ~fixpoint ~binders:(lambda_binders l) (to_reversed lparams) ret_ty_opt lbody with
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
                  cl_binders = binders;
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
              cl_binders = binders;
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
          cl_binders = binders;
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
    @param shapes      The branches of that loop, where they are known
                       otherwise than from the chains ({!Loopify_tmc.branch_along})
    @param check       Call checker for identifying recursive calls
    @param tparams     Template parameter context
    @param adopted     A body calling back into this function, to adopt as a
                       second machine entry; see {!transform_nontail}
    @param params      Function parameters [(id, type)]
    @param ret_ty      Return type
    @param body        Function body statements
    @return what the transform did; see {!nontail_result}. *)
type unlowered =
  | Declined of string
  | Left of string option

(** Why a function whose recursive call decides a branch is not made a
    machine. *)
let branch_dependency = "recursive call in a branch condition or dispatch scrutinee"

let apply_nontail_loopification ?(param_inits = []) ?fn_name ?adopted ?entered_by ?modulo_cons ?shapes ?loop
    ~varying ?binders ?parts check tparams params ret_ty body =
  let declined reason =
    {nt_body = body; nt_outcome = Lp_declined reason; nt_machine = false}
  in
  if has_recursive_branch_dependency check body then
    declined branch_dependency
  else
  let frame () =
    let machine =
      checked_frame_machine loop check (fun entered ->
          transform_nontail ?fn_name ?loop ~varying ?adopted ?entered_by ~entered ?binders ?parts check tparams params ret_ty body )
    in
    { nt_body = Option.cata fst body machine;
      nt_outcome = Lp_frame;
     
      nt_machine = Option.has_some machine }
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
            transform_tmc ~param_inits ~jumped ~varying ?parts
              ~shapes:(Option.default (chain_shapes chains) shapes)
              tparams check params ret_ty restored )
      in
      if classify check tmc = No_recursion then Some tmc
      else (
        Probe.violation "tail modulo cons plan"
          (Pp.str "a self-call survived the transform the recursion plan's chains describe");
        None )
    | None -> None
  in
  match tmc with
  | Some tmc -> {nt_body = tmc; nt_outcome = Lp_tmc; nt_machine = true}
  | None -> frame ()
  with Not_linearisable reason -> declined reason

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

let after_tail_loop ?(strategy = Lp_tail) ?survived ~tparams (f : dfun) params loop =
  report_outcome ?survived ~name:(fundef_display_name f.df_path) ~check:(survivors f) ~strategy
    (loopify_inner_lambdas ~tparams ~outer_env:params loop)

let modulo_cons_loop ~jumped ~varying ?parts ~shapes ~tparams check (f : dfun) params body =
  let r = fst f.df_path.dp_outer in
  let adopted () =
    find_adopted ~adoptable:(planned_adoptable r) ~invocations:(Recursion_plan.adopted_invocations r) body
  in
  if Option.has_some (adopted ()) || has_recursive_branch_dependency check body then None
  else
    let loop =
      transform_tmc ~jumped ~varying ?parts ~shapes tparams check params f.df_ret (Cpp_temporaries.own_stmts body)
    in
    if classify (survivors f) loop = No_recursion then Some loop else None

(** Whether the body [ad] the machine of the function [r] adopts is the
    loop [entry] its ControlIR enters: the local fixpoint's function, or
    the partner whose calls are run in place. *)
let adopts_entry r ad (entry : Control_ir.Loop.t) =
  match (ad.ad_source, entry) with
  | Fixpoint o, Member (o', 0) -> Miniml.Occurrence.equal o o'
  | Invocations _, Function g -> (
    match Recursion_plan.adopted_partner r with
    | Some i -> Common.globref_equal i.partner g
    | None -> false )
  | (Fixpoint _ | Invocations _), _ -> false

let frame_machine ~loop ?entry ~varying ?parts ~tparams check (f : dfun) params body =
  let r = fst f.df_path.dp_outer in
  let found = find_adopted ~adoptable:(planned_adoptable r) ~invocations:(Recursion_plan.adopted_invocations r) body in
  (* What the machine adopts is its ControlIR's entry: a body found where
     there is none -- a partner yielding another type than the function's --
     is left where it is, and the calls entering the machine are its loop's
     Continues. *)
  let adopted = if Option.has_some entry then found else None in
  let as_planned =
    match (adopted, entry) with
    | _, None -> true
    | Some ad, Some entry -> adopts_entry r ad entry
    | None, Some _ -> false
  in
  let survived = Option.map decline_reason found in
  let declined = Error (Left survived) in
  if has_recursive_branch_dependency check body then Error (Declined branch_dependency)
  else if not as_planned then declined
  else
    let survivors = survivors f in
    match
      checked_frame_machine (Some loop) survivors (fun entered ->
          transform_nontail ~fn_name:(fundef_display_name f.df_path) ~loop ~varying ?adopted ?entered_by:(entered_by_definition r)
            ~entered ~binders:f.df_binders ?parts check tparams params f.df_ret body )
    with
    | Some (made, _) when classify survivors made = No_recursion -> Ok (made, survived)
    | Some (made, entries) when not (has_recursive_branch_dependency survivors body) ->
      (* A machine leaving a call behind is the machine of its ControlIR
         where the calls entering it are its loop's: those it leaves are
         ordinary recursive calls there, each running a machine of its own,
         and its frames are laid out for the calls it takes alone, as a
         method's are ({!transform_method_own}). *)
      if Option.is_empty (machine_disagreement loop entries) then Ok (made, survived) else declined
    | Some _ -> Error (Declined branch_dependency)
    | None -> declined

let record_unlowered ?(unlowered = Left None) (f : dfun) body =
  let name = fundef_display_name f.df_path in
  let check = survivors f in
  match (planned_strategy (Some (fst f.df_path.dp_outer)) check body, unlowered) with
  | No_loop, _ -> ()
  | Suspended _, _ -> record_outcome name deferred_cofixpoint
  | (Tail_loop | Modulo_cons _ | Frame_stack), Declined why -> record_outcome name (Lp_declined why)
  | Tail_loop, Left survived -> ignore (report_outcome ?survived ~name ~check ~strategy:Lp_tail body)
  | (Modulo_cons _ | Frame_stack), Left survived -> ignore (report_outcome ?survived ~name ~check ~strategy:Lp_frame body)

let lower_local_tail_loops ?parts ~tparams stmts = loopify_inner_lambdas ~tail_only:true ?parts ~tparams stmts

let lower_function_locals ~tparams params body = loopify_inner_lambdas ~tparams ~outer_env:params body

let local_frame_machine ~member ~name ~binders ~varying ?parts ~tparams check params ret_ty body =
  let name = Id.to_string name in
  Option.bind
    (checked_frame_machine (Some (Control_ir.Loop.Member (fst member, snd member))) check (fun entered ->
         transform_nontail ~fn_name:name ~loop:(Control_ir.Loop.Member (fst member, snd member)) ~varying ~binders
           ~entered_by:(entered_by_member member) ~entered ?parts check tparams
           params ret_ty body ) )
    (fun (machine, _) ->
      if classify check machine = No_recursion then
        Some (loopify_inner_lambdas ~tparams (report_outcome ~name ~check ~strategy:Lp_frame machine))
      else None )

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
    @param varying        Which of the receiver and the parameters the loop
                          varies, as its ControlIR says
    @param controlled     Whether a loop tail modulo cons or a machine takes
                          the calls its ControlIR continues by, and builds
                          its cells as its turns do, rather than every call
                          of the method's
    @return An [Fmethod] field with the loopified body *)
let value_receiver = "recursive call passes a value-type receiver, whose address cannot be stored in a frame"

let rebuilt_receiver_read =
  "recursive call makes the receiver it passes and reads the receiver in another argument, which parking it overwrites"

(** The position of the receiver of the method [mf] among the arguments a
    C++ call of it writes: the registry's
    ({!Cpp_names.lookup_method_this_pos}).  The method's own [this_pos]
    counts the arrows of its ML type, and an erased one before the receiver
    -- a dictionary, a type binder kept under Conservative Types -- takes
    no argument.  A static method has no receiver to strip from a call: its
    calls never carry more arguments than it has parameters, so position
    [0] is never read. *)
let receiver_position mf =
  match mf.mf_receiver with
  | Static -> 0
  | Instance r -> (
    match Option.bind mf.mf_globref Cpp_state.is_registered_method with
    | Some (_, pos) -> pos
    | None -> r.this_pos )

let transform_method_own ~varying ?parts ~park ~tparams ~self_ty mf =
  (* [tparams] arrives holding only the enclosing struct's parameters.  A
     method's body is written under its own template header too, and a
     parameter declared there is the one most likely to constrain how the body
     may be rewritten -- a callable argument is a method parameter, never a
     struct one. *)
  let tparams = tparams @ mf.mf_tparams in
  let n_params = List.length mf.mf_params in
  let this_pos = receiver_position mf in
  let name = Id.to_string mf.mf_name in
  let basic_check =
    method_checker ~n_params ~has_self_param:false ~this_pos mf.mf_globref
  in
  let strategy = planned_strategy mf.mf_globref basic_check mf.mf_body in
    ( match strategy with
    (* A suspended method returns in O(1) stack frames, as a function does. *)
    | Suspended _ ->
      record_outcome name deferred_cofixpoint;
      Fmethod mf
    | No_loop ->
      Fmethod mf
    | Tail_loop | Modulo_cons _ | Frame_stack ->
      let self_id = id_self in
      let body_with_self = List.map (this_to_self_stmt self_id) mf.mf_body in
      let self_check =
        method_checker ~n_params ~has_self_param:true ~this_pos mf.mf_globref
      in
      (* A tail call whose receiver is a value made in the turn ([t::n(...)])
         is linearised by parking the value in a local that outlives the
         loop and recursing on that local instead, so the pointer stored for
         [_self] stays valid across the back-edge.  The parking assignment
         happens first, so a turn whose other arguments read the receiver is
         declined before this ({!rebuilt_receiver_read}).  Which turns park is the plan's [park] ({!Control_ir.rebuilt}); every
         other turn passes a receiver derived from the loop's parameters. *)
      let self_store_ty =
        let rec pointee = function
          | Tref (_, t) | Tconst t -> pointee t
          | Tptr t | Tshared_ptr t -> Some (strip_ref_and_const_type t)
          | _ -> None
        in
        pointee self_ty
      in
      let id_self_store = Id.of_string "_self_store" in
      let park_receivers body =
        let parked = ref 0 in
        let replace_at pos x l = List.mapi (fun i y -> if i = pos then x else y) l in
        let is_self r =
          match mf.mf_globref with Some sr -> Common.globref_equal r sr | None -> false
        in
        let parks cs = match cs.cs_occurrence with Some o -> List.exists (Miniml.Occurrence.equal o) park | None -> false in
        (* [park e] returns the rewritten self-call, with its value receiver
           replaced by a reference to the parking slot, or [None]. *)
        let park e =
          match e with
          | CPPfun_call (cs, CPPglob (r, targs, x), args)
            when is_self r && List.length (to_reversed args) > n_params && parks cs -> (
            let args_normal = call_args args in
            match List.nth_opt args_normal this_pos with
            | Some recv ->
              let args' =
                List.rev (replace_at this_pos (CPPvar id_self_store) args_normal)
              in
              Some (recv, CPPfun_call (cs, CPPglob (r, targs, x), of_reversed args'))
            | None -> None )
          | _ -> None
        in
        let rec go_stmt s =
          match s with
          | Sreturn (Some e) when park e <> None ->
            let (recv, call) = Option.get (park e) in
            incr parked;
            Sblock [Sasgn (id_self_store, Existing, recv); Sreturn (Some call)]
          | _ -> map_stmt (fun e -> e) go_stmt Fun.id s
        in
        let body' = List.map go_stmt body in
        (body', !parked)
      in
      let parked_body, parked =
        match (strategy, self_store_ty) with
        | Tail_loop, Some _ -> park_receivers body_with_self
        | _ -> (body_with_self, 0)
      in
      if parked <> List.length park then begin
        Probe.violation "control lowering"
          Pp.(str "the tail loop of the method " ++ str name ++ str " has a turn making its receiver that no tail call parks");
        record_outcome name (Lp_declined value_receiver);
        Fmethod mf
      end else
      let body_with_self, self_store_ty = if parked = 0 then (body_with_self, None) else (parked_body, self_store_ty) in
      let self_param = (self_id, self_ty) in
      let augmented_params = self_param :: mf.mf_params in
      let lowered =
        match strategy with
        | Tail_loop ->
          Some
            (report_outcome ~name ~check:(method_survivors mf) ~strategy:Lp_tail
               (let loop = Option.bind mf.mf_globref function_loop in
                checked_tail_loop loop (fun jumped ->
                    transform_tail ~param_inits:[(self_id, CPPthis)] ~jumped ~varying ?parts tparams
                      (planned_jumps loop self_check) augmented_params mf.mf_ret_type body_with_self ) ) )
        | Modulo_cons _ | Frame_stack ->
          let fn_name = Some name in
          let loop = Option.bind mf.mf_globref function_loop in
          (* Lowered from its ControlIR, a method's calls taken are those its
             loop continues by, and the cells built around them its turns'. *)
          let check = planned_jumps loop self_check in
          let shapes =
            Option.map (fun t -> Loopify_tmc.control_shapes (Control_ir.continues_into t)) (Option.bind loop Lower_control.loop)
          in
          let r =
            apply_nontail_loopification
              ?entered_by:(Option.map entered_by_function mf.mf_globref)
              ~param_inits:[(self_id, CPPthis)]
              ~binders:
                ( (match mf.mf_receiver_binder with Some b -> [(self_id, b)] | None -> [])
                @ mf.mf_binders )
              ?fn_name ?modulo_cons:(modulo_cons_chains strategy) ?shapes ?loop ~varying ?parts
              check tparams
              augmented_params mf.mf_ret_type body_with_self
          in
          let body' =
            report_outcome ~name ~check:(method_survivors mf) ~strategy:r.nt_outcome
              r.nt_body
          in
          if r.nt_outcome = Lp_frame && not r.nt_machine then None else Some body'
        | No_loop | Suspended _ -> CErrors.anomaly (Pp.str "loopify: no loop cannot appear here")
      in
      match lowered with
      | None -> Fmethod mf
      | Some body' ->
      (* Declare the parking slot outside the loop so the pointer taken to it
         on the back-edge stays valid for the next iteration. *)
      let body' =
        match self_store_ty with
        | Some ty -> Sdecl (id_self_store, ty, None) :: body'
        | None -> body'
      in
      (* A loop varying the receiver initialises its own copy of it from
         [this]; any other reads [_self] as it was on entry. *)
      if List.exists (Id.equal self_id) (free_vars_body body') then
        let init_self = Sasgn (self_id, Declare (self_ty, None), CPPthis) in
        Fmethod {mf with mf_body = init_self :: body'}
      else
        Fmethod {mf with mf_body = body'} )

let record_unlowered_method mf =
  let check = method_survivors mf in
  let name = Id.to_string mf.mf_name in
  match planned_strategy mf.mf_globref check mf.mf_body with
  | No_loop -> ()
  | Suspended _ -> record_outcome name deferred_cofixpoint
  | Tail_loop -> ignore (report_outcome ~name ~check ~strategy:Lp_tail mf.mf_body)
  | Modulo_cons _ | Frame_stack -> ignore (report_outcome ~name ~check ~strategy:Lp_frame mf.mf_body)

(** Check the pointer fields of each constructor struct of [ds] against
    those planned before rendering ({!Loopify_analysis.agree_ptr_fields}). *)
let check_pointer_fields ds =
  let rec fields (fld, _, _) =
    match fld with
    | Fnested_struct (id, sub_fields) ->
      let var_fields = List.filter_map (fun (f, _, _) -> match f with Fvar (_, ty) -> Some ty | _ -> None) sub_fields in
      let ptr_fields =
        List.filter_map Fun.id
          (List.mapi
             (fun i ty ->
               match ty with
               | Tshared_ptr (Tglob (r, _, _)) when Common.globref_equal r ds.ds_ref -> Some (Recursive i)
               | Tshared_ptr _ -> Some (Boxed i)
               | _ -> None )
             var_fields )
      in
      if ptr_fields <> [] then agree_ptr_fields ds.ds_ref (Id.to_string id) ptr_fields;
      List.iter fields sub_fields
    | _ -> ()
  in
  List.iter fields ds.ds_fields
