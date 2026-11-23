(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Applications: a call of a global or a local, its arguments generated
    against the callee's parameters, a class field projected through an
    instance, and partial applications eta-expanded into closures
    ({!eta_fun}).  One of the modules lowering Core
    bodies to CppIR that {!Lower_expr} drives; it calls back into
    expression and statement lowering through {!Knot}. *)

open Base.Common
open Names
open Base.Table
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query
open Knot
open Lambda
module Typed = Cpp_ir.Typed

(** The types of the members of the local fixpoint groups being generated
   that recurse at a ground instance ({!Base.Table.is_erased_fix_group}), as the
   environment binds them: a call of one is written at its own instance, and
   its arguments are adapted to the erased parameters. *)
let erased_member_types : Core.Type.t list ref = Base.State.cell Base.State.Unit []

(** Record the members [ids] of the local fixpoint [occ] -- and the type
   [let_ty] of the name it is bound to, if any -- in {!erased_member_types}
   where the group is one.  Kept by identity, so a type recorded for one
   group is no other binding's. *)
let register_erased_members ?let_ty occ ids =
  if Base.Table.is_erased_fix_group occ then
    erased_member_types :=
      (match let_ty with Some t -> [t] | None -> []) @ List.map snd (Array.to_list ids) @ !erased_member_types

(** Whether the variable [i] is a member of a group {!erased_member_types}
   knows, its type erasing a domain. *)
let erased_member cx i =
  match get_env_type_opt cx i with
  | Some (Core.Type.Arrow _ as t) ->
    List.memq t !erased_member_types && List.exists Base.Core_util.has_unknown (core_domains t)
  | _ -> false

(** [expr], the argument [a] to a parameter of type [param_ty] that
   erased a domain ({!erased_member_types}), adapted to it -- unless it is
   a variable already of that type, which an adapter would only wrap again at
   every call that passes it on. *)
let adapt_to_erased_param cx env param_ty a expr =
  match a with
  | Core.Expr.Bound_variable {index = j; _}
    when (match get_env_type_opt cx j with
          | Some t -> Types.cpp_of_core cx env t = Types.cpp_of_core cx env param_ty
          | None -> false) -> expr
  | _ -> Coerce.erase_fn_arg_for_param cx env param_ty a expr

(** [stmts] with the declaration of the local [id] standing for the Core
   binder [b]. *)
let declaring id b stmts =
  List.map
    (fun (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t ->
      match s with
      | Bind_variable (x, Declare (ty, None), e) when Id.equal x id -> Bind_variable (x, Declare (ty, b), e)
      | s -> s )
    stmts

(** [made_of occurrence e] is the call [e] recording the Core call it is
   made of; any other expression unchanged. *)
let made_of occurrence : Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Expr.t = function
  | Call (cs, f, args) -> Call ({cs with occurrence = Some occurrence}, f, args)
  | e -> e

(** [erased_lambda l ~params ~ret ~body] is the lambda [l] rewritten to
   take [params] (source order) and return [ret], with [body] doing whatever
   casting back the erasure of its parameters now needs, and with no template
   parameters of its own: a polymorphic function object cannot stand where an
   erased slot deduces its type. *)
let erased_lambda (l : Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t) ~params ~ret ~body : Cpp_ir.Lowered.Expr.t =
  Lambda {l with type_params = []; params; return_type = ret; body}

(** The instance parameter, the class and its one method, where the variable
   [i], read at [occ] at the head of an application, is a singleton class's
   dictionary, as Core decided it ({!Core_plan.Elaborate.singleton_dictionary_call});
   {!Calls.singleton_dictionary} is the traversal's own reading, checked against
   it. *)
let singleton_call cx env i occ =
  let live () =
    Option.map (fun (_, c, m) -> (c, m))
      (Calls.singleton_dictionary cx env (Core.Expr.Bound_variable {index = i; occurrence = occ})) in
  match Core_plan.Elaborate.singleton_dictionary_call ~walk:(elaborations cx) ~live occ with
  | Some (c, m) -> Option.map (fun id -> (id, c, m)) (Base.Common.get_db_name_opt i env)
  | None -> None

(** Call class field [x] as a static member of the instance struct [inst].

   Rocq hands a projection over already applied where the instance is
   concrete, so the term is an ordinary application and not the single-branch
   match a projection through an instance {e variable} extracts to; the C++ is
   the same either way. *)
let project_through_instance cx env (use : Core.Global_use.t) args (projection : Core_plan.Elaborated_call.static_projection) :
  Cpp_ir.Lowered.Expr.t =
  let inst = List.nth args projection.instance in
  let x = use.callee and tys = Base.Core_util.written_type_args use in
  let operands =
    List.filter
      (fun a ->
        match a with
        | Core.Expr.Erased_value _ -> false
        | _ -> not (is_typeclass_instance_arg ~lex:(current_lexenv cx ()) a) )
      args
  in
  (* The instance declares each method as a member template over the method's
     own type variables -- the class's parameters are the instance, not
     parameters of its methods -- so the call's type arguments minus the
     class's are the method's.  The class's stand in front of the dictionary
     in the projection's type, erased.  They are given explicitly rather than
     deduced: a method declares its continuation as a [std::function], which
     a closure does not deduce, and [ret] mentions its variable only in its
     result. *)
  let targs =
    let by_var = List.map (fun (v, t) -> (v, Types.cpp_of_core cx env t))
      (Base.Core_util.Var_types.bindings tys) in
    Core_plan.Template_application.to_list
      (Core_plan.Template_application.plan
         (Core_plan.Callable_abi.projection (Lowering_state.callables cx) Calls.projection_abi x)
         ~instance:(fun _ -> None)
         ~scheme:(fun v -> Core.Scheme.Var.assoc_opt v by_var) )
  in
  (* What each operand is written into.  [tys] leads with the carrier, which
     is how the field's own type numbers the class parameter, so the single
     substitution that instantiates the method also resolves [m A] -- and
     without it an operand that spells its type for the first time, a match
     whose branches have to agree on one return type, is built at whatever
     the enclosing declaration returns.  An argument is not a tail position,
     so that is never the right answer; see {!Coerce.position_cpp_ty}.

     Only a suffix as long as the operand list is safe to read. *)
  let operand_core_tys =
    let doms = projection.domains in
    let extra = List.length doms - List.length operands in
    if extra >= 0 then List.filteri (fun i _ -> i >= extra) doms else []
  in
  (* The instance is a type: an applied one -- [TFunctor_option
     TFunctor_box] -- is spelled as the template argument it would be. *)
  let inst_expr : Cpp_ir.Lowered.Expr.t =
    match Calls.core_arg_to_template_type cx env inst with
    | Some t -> Type_name t
    | None -> gen_expr cx env inst
  in
  Cpp_ir.Build.call
    (Scope (inst_expr, Base.Common.id_of_global Term x, targs))
    (List.mapi
       (fun i a ->
         let expected = Types.param_expected_cpp_ty cx env operand_core_tys i in
         let slot =
           {Slot.empty_slot with Slot.expected_core_ty = List.nth_opt operand_core_tys i}
         in
         with_cpp_return_type cx expected (fun () ->
             gen_expr cx ?expected_ty:expected ~slot env a ) )
       operands )

(** [gen_call_args ~slot ?expected_ty env id plan] -- the C++ arguments of
    the call of the global [id] that [plan] describes, each generated against
    the parameter it is passed at.  The dictionaries' promoted variables are in scope for them. *)
let gen_call_args cx ~slot ?(expected_ty : Cpp_ir.Lowered.Type.t option) ~written_by_var env id plan :
    Typed.t list =
  let {
    Calls.instantiated =
      {
        Core_plan.Elaborated_call.call =
          {Core_plan.Elaborated_call.regular = regular_core_args; callee_type = fn_core_ty; _} as call;
        tys;
        params = fn_param_core_tys;
        params_orig = fn_param_core_tys_orig;
        subst_index_of_orig;
        _
      };
    expected_result = expected_result;
    instance_families = instance_families;
    tvars = tvars;
    result_tvar_map = result_tvar_map;
    _
  } = plan in
  let leading_params = Core_plan.Elaborated_call.leading_params call in
  List.mapi (fun i core_arg : Typed.t ->
    match strip_magic core_arg with
    | Core.Expr.Erased_value _ -> Typed.of_node @@ (
      (* An erased value, boxed.  At a function-typed parameter it is an
         erased function -- [bif : obj -> obj -> obj] is [sum1] once [obj]
         is [Type -> Type] -- which is called, so it is a callable of the
         declared arity handing back a box. *)
      match
        Core_plan.Param_pos.nth fn_param_core_tys_orig
          (Core_plan.Param_pos.of_regular ~leading:leading_params i)
      with
      | Some pt when count_core_value_arrows pt > 0 ->
        Cpp_ir.Build.lambda
          (List.init (count_core_value_arrows pt) (fun _ ->
               ((Reference (Lvalue, Const Auto) : Cpp_ir.Lowered.Type.t), None) ))
          None
          [Return (Some Cpp_passes.Erasure.empty_box)]
          ~capture:Stored
      | _ -> Cpp_passes.Erasure.empty_box )
    | _ ->
    let ({Calls.index = param_index; param = param_core_ty; expected = arg_expected_ty;
           ret = ret; tvar_erased = param_tvar_erased; written_by_call = param_written_by_call;
           deduced_callable = deduced_callable; expected_subst} : Calls.argument_position) =
      Calls.argument_position cx ~local_callable:(Calls.local_callable cx env) env id
        plan i core_arg
    in
    let param_expected_subst () = expected_subst in
    (* {b Lambda arity limiting.}  When a lambda argument has more binders
       than the callee's parameter type has top-level arrows, the extra
       binders come from the return type being a function (instantiated
       from a type variable).  For example, [fold_right]'s callback type
       is [B -> A -> A]; when [A = nat -> nat], the lambda
       [fun t acc => fun x => body] has 3 binders but the parameter has
       only 2 arrows.  Flattening all 3 into a single C++ lambda produces
       a 3-arg function, which doesn't match the 2-arg is_invocable_v constraint.

       Fix: insert an [Core.Expr.Lambda_group_barrier] after the expected number of
       binders so that [collect_lams] in [gen_expr] stops there.  The
       inner binders become a returned inner lambda.  We use the
       {i non-substituted} parameter type to count arrows, because type
       variable substitution would inflate the count (e.g. [Core.Type.Variable A]
       becoming [Core.Type.Arrow(nat, nat)] adds a spurious arrow).

       The lambda is lowered against its slot, the parameter at the call's
       instantiation ([arg_expected_ty]): its body returns into the slot's
       codomain ({!Lambda.gen_lambda}'s destination), so nothing adapts it
       afterwards.  (A return annotation the split used to add here was
       dropped again by {!Cpp_passes.Simplify}: a lambda that only returns a
       lambda hands it back unannotated.) *)
    let core_arg =
      match core_arg with
      | Core.Expr.Lambda _ -> (
        match Core_plan.Param_pos.nth fn_param_core_tys_orig param_index with
        | Some param_ty ->
          let rec count_arrows = function
            | Core.Type.Arrow {result = rest; _} -> 1 + count_arrows rest
            | _ -> 0
          in
          let expected = count_arrows param_ty in
          let actual = Base.Core_util.nb_lams core_arg in
          if expected > 0 && actual > expected then
            let outer_ids, inner_body = Base.Core_util.collect_n_lams expected core_arg in
            Base.Core_util.named_lams outer_ids
              (Core.Expr.Lambda_group_barrier {value = inner_body; occurrence = Core.Occurrence.fresh ()})
          else core_arg
        | None -> core_arg )
      | _ -> core_arg
    in
    let arg_expected_core_ty =
      match param_core_ty with
      | Some core_ty when not (core_type_contains_erased core_ty) -> Some core_ty
      | _ -> slot.Slot.expected_core_ty
    in
    let arg_typed =
      with_cpp_return_type cx ret (fun () ->
          Knot.gen_expr_typed cx ?expected_ty:arg_expected_ty
            ~slot:
              { slot with
                Slot.expected_core_ty = arg_expected_core_ty;
                call_result = expected_result;
                stated_core_ty = param_core_ty }
            env core_arg )
    in
    let expr = arg_typed.expr in
    (* The slot the argument fills: the parameter at the call's
       instantiation, a forwarding reference for a deduced callable, a
       template parameter for an inline mapping's parameter at a type
       variable. *)
    let arg_slot : Cpp_ir.Lowered.Slot_type.t =
      Calls.argument_slot cx env id ~deduced_callable ~written_by_var ~expected:arg_expected_ty
        (Core_plan.Param_pos.nth fn_param_core_tys_orig param_index)
    in
    let expr : Cpp_ir.Lowered.Expr.t =
      match param_core_ty with
      | Some param_ty when not deduced_callable ->
        Coerce.erase_fn_arg_for_param cx env param_ty core_arg expr
      | _ -> expr
    in
    (* A callable at an inline mapping's parameter declared at a type
       variable arrives named ({!Coerce.mapping_name_built}), at the
       instantiation where it can be spelled here, as a type argument
       spells it. *)
    let expr : Cpp_ir.Lowered.Expr.t =
      if not (Base.Table.is_inline_custom id) then expr
      else
        match (Option.map resolve_meta (Core_plan.Param_pos.nth fn_param_core_tys_orig param_index), expr) with
        | _, Function_value _ -> expr
        | Some (Core.Type.Variable _), _ -> (
          match Option.map resolve_meta param_core_ty with
          | Some (Core.Type.Arrow _ as t) ->
            let spelled =
              match Types.template_params_of_core cx ~site:Cpp_ir.Types.Through_tvar env [t] with
              | [(Function _ as f)]
                when Types.names_only_scoped_tvars cx f && not (Base.Type_util.has_tany_written f) ->
                Some f
              | _ -> None
            in
            let value = if expr == arg_typed.expr then arg_typed else Typed.of_node expr in
            Coerce.into_slot ~origin:Mapping_name value (Template_parameter spelled)
          | _ -> expr )
        | _ -> expr
    in
    (* A methodified callee is spelled [recv.f(rest)], and [std::any] has no
       members: unlike every other argument, the receiver cannot arrive as a
       box at all.  What says that it does is the declaration the receiver
       came out of -- a method registered as returning [std::any] -- and the
       parameter's type is what says what the box holds. *)
    let expr : Cpp_ir.Lowered.Expr.t =
      let receiver_is_boxed =
        (* The receiver's own Core type has to say it is gone -- a projection
           out of a dependent pair is a bare type variable, and extraction
           leaves a [Core.Type.Erased] behind. *)
        ( match
            Option.map (fun t -> Types.cpp_of_core cx env t)
              (infer_core_body_type (strip_magic core_arg))
          with
        | Some t -> Cpp_ir.Types.prints_as_any t
        | None -> false )
        &&
        (* And it has to have come out of an accessor on a value that
           carries erasure: a [SigT<std::any, std::any>] hands back a box, a
           [SigT<List<uint64_t>, List<uint64_t>>] hands back a list.  A call
           whose arguments are all concrete does not qualify however its Core
           type reads -- a free template function's result is resolved by
           the type arguments the call site states. *)
        match strip_magic core_arg with
        | Core.Expr.Apply {callee = g; arguments = rargs} -> (
          match strip_magic g with
          | Core.Expr.Global _ -> Erasure.app_reads_erased_value cx env rargs
          | _ -> false )
        | _ -> false
      in
      match Unit_plan.Cpp_names.lookup_method_this_pos id with
      | Some pos
        when Core_plan.Param_pos.equal (Core_plan.Param_pos.of_receiver pos) param_index
             && receiver_is_boxed -> (
        match param_expected_subst () with
        | Some into when not (Cpp_ir.Types.prints_as_any into) ->
          Coerce.coerce cx ~from:Any ~into expr
        | _ -> expr )
      | _ -> expr
    in
    let expr : Cpp_ir.Lowered.Expr.t =
      if param_tvar_erased && not param_written_by_call then
        (* Say where the value is coming from where the binder's own type
           says: an argument that is already a box is left alone. *)
        let from =
          match core_arg with
          | Core.Expr.Bound_variable {index = j; occurrence = occ} ->
            Binders.planned_binder_type_or_derive cx ~use:"argument's type" ~agree:( = ) env j occ
          | _ -> None
        in
        Coerce.coerce cx ~term:core_arg ?from ~into:Any expr
      else expr
    in
    (* Wrap void calls as values only when the expression will be used
       as a value (not in monadic parameter handler which places it in
       statement position inside a lambda). *)
    let as_value () =
      match core_arg with
      (* An inline custom's monadic [unit] parameter in sequential mode is a
         computation its text runs -- [stm::atomically([&] { return %a0; })]
         -- and a lambda may return a [void] call. *)
      | _
        when is_inline_custom id
             && (match param_core_ty with
                 | Some t -> is_monadic_core_type t && Monadic.core_type_is_void_call t
                 | None -> false) ->
        expr
      | a when Monadic.core_value_is_void_call cx a ->
        (* Don't wrap eta-expanded lambdas (partial applications) — they
           are function VALUES, not void call results. *)
        ( match expr with
        | Lambda _ -> expr
        | _ -> Monadic.wrap_void_call_as_value expr )
      | _ -> expr
    in
    (* A bare local variable known to be boxed as [std::any]
       ({!Binders.read_is_boxed}) — e.g. a leaf pulled out of an erased-pair
       destructure — passed directly to a plain global function whose
       parameter type is concrete.  Mirrors the equivalent check for
       non-global callees (~[Core.Expr.Bound_variable j when Core_plan.Escape.IntSet.mem ...] above). *)
    let core_arg_is_erased_rel =
      match core_arg with
      | Core.Expr.Bound_variable {index = j; occurrence = occ}
      | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = j; occurrence = occ}; _}
      | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = j; occurrence = occ}; _}
      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = j; occurrence = occ}; _} ->
        Binders.read_is_boxed cx j occ
      | _ -> false
    in
    let passed =
    match param_core_ty with
    | Some param_ty
      when ( Erasure.core_body_returns_erased_field core_arg || core_arg_is_erased_rel
           (* A component read out of a pair that was itself recovered from
              a box is a [std::any] whatever its Core type says, and the
              emitted expression is the evidence -- see
              {!Erasure.yields_boxed_component}. *)
           || Erasure.yields_boxed_component (as_value ()) )
           && not (match param_ty with
                   | Core.Type.Global_app {head = g; _} -> Base.Table.is_promoted_type_var g
                   | _ -> false)
           (* [param_ty] comes from the callee's own (call-site-substituted)
              type signature, whose [Core.Type.Variable] indices are not anchored to this
              function's [tvars] scope. When conversion produces an
              unresolved C++ [Variable (Index (_, None))] (would print as a bogus template
              parameter like "T3"), we cannot build a meaningful concrete
              cast here — skip this branch and fall back to [as_value ()]
              unchanged; a later pass (e.g. [gen_match_branch]'s field
              substitution) supplies the correct cast at its own,
              properly-scoped [tvars]. *)
           && Types.erase_unresolved_tvars (Types.cpp_of_core cx env param_ty)
              = Types.cpp_of_core cx env param_ty ->
      let cpp_ty = Types.cpp_of_core cx env param_ty in
      ( match Convert.strip_ns_global_app cpp_ty with
      | Entity_application (g, [_], _) when is_list_global g && not (Base.Table.is_custom g) ->
        let list_any_ty : Cpp_ir.Lowered.Type.t =
          match cpp_ty with
          | In_namespace (ns_g, _) -> In_namespace (ns_g, Entity_application (g, [Any], []))
          | _ -> Entity_application (g, [Any], [])
        in
        (* [as_value ()] may already have unboxed the erased value to the
           canonical element-erased shape (the [Core.Expr.Bound_variable] case of [gen_expr]
           does this for a variable bound to an erased field).  Casting
           again would re-box that concrete list into a fresh [std::any]
           only to unbox it — mirror the custom-list branch below and reuse
           the existing cast.  It may also have gone the whole way and
           recovered the concrete list already ({!Coerce.coerce} does this for a
           value crossing out of a box), in which case there is nothing
           left to convert. *)
        ( match as_value () with
        | Converting_construct (t, _) as recovered when cpp_ty_eq t cpp_ty ->
          recovered
        | Any_cast _ as already_cast ->
          Cpp_passes.Erasure.converting_ctor cpp_ty [already_cast]
        | v ->
          Cpp_passes.Erasure.converting_ctor cpp_ty [Cpp_passes.Erasure.unbox list_any_ty v] )
      | Entity_application (g, [_], _) when Base.Type_util.is_custom_list_global g ->
        let clean_cpp_ty = Convert.clean_self_ns cpp_ty in
        (* Custom-extracted list (e.g. [std::deque]) is boxed as [std::any]
           with fully-erased elements at runtime ([deque<pair<any,any>>]).
           Cast the inner value to that erased representation, matching what
           [gen_match_branch]'s field substitution stores. *)
        let erased_ty : Cpp_ir.Lowered.Type.t =
          (* Canonical erased shape is [deque<std::any>] -- a bare [std::any]
             per element, not a structure-preserving [deque<pair<any,any>>]
             (see the matching invariant in [gen_expr]'s [Core.Expr.Bound_variable]/[Core.Expr.Coerce]
             cases).  Using the structure-preserving erasure here would
             disagree with a sibling producer for the same Coq list type
             that already erased to the flat shape, and — when [as_value ()]
             is itself already an [any_cast] to the flat shape (added by
             [gen_expr] above) — would additionally double-wrap it in a
             second, incompatible [any_cast]. *)
          match clean_cpp_ty with
          | In_namespace (ns_g, Entity_application (g, [_], _)) ->
            In_namespace (ns_g, Entity_application (g, [Any], []))
          | Entity_application (g, [_], _) ->
            Entity_application (g, [Any], [])
          | _ -> clean_cpp_ty
        in
        let inner = match as_value () with
          | Any_cast _ as already_cast -> already_cast
          | v -> Cpp_passes.Erasure.unbox erased_ty v
        in
        (* When the callee is a REAL function whose parameter has a CONCRETE
           element type — a wholesale-boxed opaque element
           ([triples_le_max(const std::deque<rgb>&)]), OR a structural element
           whose concrete component must be preserved for a POLYMORPHIC/template
           callee ([nodupKeys<T1>(const std::deque<std::pair<std::string,T1>>&)],
           whose [std::string] key cannot be erased to [std::any] or template
           argument deduction fails) — the fully-erased [inner] neither converts
           nor deduces against it.  Route it through [crane_container_cast],
           which builds the concrete-element container (unboxing wholesale-boxed
           elements at runtime; for structural elements it still compiles and
           lets deduction succeed).

           Inline-custom callees (e.g. [length]'s [.size()]) splice the
           argument into a template and work on the erased container, and a
           callee whose parameter element is ALREADY fully erased
           ([deque<pair<any,any>>]) needs no conversion — both keep [inner]. *)
        let needs_concrete =
          (not (Base.Table.is_inline_custom id))
          &&
          match Convert.strip_ns_global_app clean_cpp_ty with
          | Entity_application (_, [et], _) ->
            et <> Cpp_passes.Erasure.erase_type_to_any et
          | _ -> false
        in
        if needs_concrete then begin
          (* When the callee's OWN declared (unsubstituted) parameter type
             is still generic here (a template function like
             [nodupKeys<T1>]), its C++ declaration never boxes the element
             (a bare type variable never recurses).  This call site's
             [clean_cpp_ty] was built from the call-site-substituted
             concrete type though, so it may judge the (now concrete,
             possibly recursive) element as boxed — disagreeing with the
             generic declaration and breaking template argument deduction.
             Suppress boxing here to match the declaration. *)
          let callee_generic_here =
            match Core_plan.Param_pos.nth fn_param_core_tys_orig param_index with
            | Some t -> Base.Type_util.core_type_contains_tvar t
            | None -> false
          in
          Container_cast (clean_cpp_ty, inner, callee_generic_here)
        end
        else inner
      (* The value is boxed; recover it at the parameter's type.  Going
         through {!Coerce.coerce} rather than casting outright keeps the one rule
         that a destination which is itself a name for the box -- [using sel
         = std::any] -- is not a recovery target: [any_cast<sel>] reads a box
         that was never doubly wrapped and throws. *)
      | _ -> Coerce.coerce cx ~from:Any ~into:cpp_ty (as_value ()) )
    (* Monadic parameter (reified mode only): the callee expects
       [shared_ptr<ITree<R>>].  If the argument already produces a reified
       tree, pass through as-is; otherwise wrap in [ITree<R>::ret()]. *)
    | Some param_ty when cx.ctx.input.itree_mode = Reified
        && is_monadic_core_type param_ty
        && not (Monadic.is_reified_monadic_expr cx core_arg) ->
      let r_core = Monadic.extract_itree_result_core param_ty in
      let r_cpp = Types.cpp_of_core cx env r_core in

      let itree_ty = Monadic.mk_itree_type r_cpp in
      (* [expr] is a value unless the thing it calls was void-ified, in
         which case it is a statement and the tree carries [tt] instead.
         Only a genuinely valueless result gets the nullary [ret()]: a
         [unit] one has [monostate] to carry, and a tree spelled
         [ITree<void>] would not match the [ITree<Unit>] declared for it. *)
      let no_value = r_cpp = Void || core_type_is_void r_core in
      let as_statement = no_value || Monadic.core_expr_is_void_call cx core_arg in
      let ret_expr =
        if no_value then Monadic.mk_itree_ret Void []
        else if as_statement then Monadic.mk_itree_ret r_cpp [Monadic.mk_tt_expr ()]
        else Monadic.mk_itree_ret_for_value r_cpp r_core expr
      in
      let body : Cpp_ir.Lowered.Stmt.t list =
        if as_statement then [Expression expr; Return (Some ret_expr)]
        else [Return (Some ret_expr)]
      in
      Cpp_ir.Build.iife (Some itree_ty) body
    (* Void-ified function reference passed as callback to polymorphic
       HOF where the ORIGINAL (non-substituted) parameter codomain is a
       type variable (not concrete unit).  The C++ definition uses a
       template type parameter constrained with is_invocable_v, so the void
       function needs wrapping to return std::monostate.  When the original
       codomain IS concrete unit, the constraint uses void which already
       accepts void-returning functions. *)
    | Some param_ty
      when (match core_arg with
            | Core.Expr.Global {callee = r; _}
            | Core.Expr.Coerce {value = Core.Expr.Global {callee = r; _}; _}
            | Core.Expr.Boxed_value {value = Core.Expr.Global {callee = r; _}; _}
            | Core.Expr.Lambda_group_barrier {value = Core.Expr.Global {callee = r; _}; _} ->
              Monadic.is_void_ified_ref r
            | _ -> false)
           && (match param_ty with Core.Type.Arrow _ -> true | _ -> false)
           && core_type_is_unit (core_codomain param_ty)
           && (match Core_plan.Param_pos.nth fn_param_core_tys_orig param_index with
               | Some orig_pt ->
                 not (core_type_is_unit (core_codomain orig_pt))
               | None -> false) ->
      let dom_core_tys =
        let rec collect acc = function
          | Core.Type.Arrow {parameter = t; result = rest} ->
            ( match resolve_meta t with
            | Core.Type.Erased _ -> collect acc rest
            | t -> collect (t :: acc) rest )
          | _ -> List.rev acc
        in
        collect [] param_ty
      in
      let dom_cpps =
        List.map
          (fun t -> Types.cpp_of_core cx env t)
          dom_core_tys
      in
      let params =
        List.mapi
          (fun j ty ->
            ((Reference (Lvalue, Const ty) : Cpp_ir.Lowered.Type.t), Some (Id.of_string (Printf.sprintf "_wa%d" j))))
          dom_cpps
      in
      let args =
        List.map (fun (_, id) : Cpp_ir.Lowered.Expr.t -> Local (Option.get id)) params
      in
      let body : Cpp_ir.Lowered.Stmt.t list =
        [ Expression (Call (Cpp_ir.Build.signature ~nargs:0 (), expr, args));
          Return (Some (Monadic.mk_tt_expr ())) ]
      in
      Cpp_ir.Build.lambda params None body ~capture:Runs_in_place
    | _ -> as_value ()
    in
    let passed = Typed_checks.adapted ~before:arg_typed arg_expected_ty passed in
    Typed_checks.fit cx ~site:"argument" passed arg_slot;
    passed
  ) regular_core_args

(** The call of [f] applied to [args].  A global callee is called as
    {!Calls.lower_call} plans it: missing value arguments are
    eta-expanded into a closure taking them, and arguments past the
    callee's declared arrows are applied to the primary call's result.  Any
    other callee (a local, a projection) is called directly with its erased
    arguments dropped and its class-typed ones moved into its template
    arguments, the call split the same way where the callee's type has fewer
    value arrows, made through the canonical
    [std::function<std::any(std::any...)>] adapter where the callee's type
    erases to [std::any], and its result recovered from a box where the
    callee's codomain is erased. *)
let eta_fun cx ?(slot = Slot.empty_slot) ?(expected_ty : Cpp_ir.Lowered.Type.t option) env f args :
    Typed.t =
  let core_args = args in

  let rec get_eta_args dom args =
    match (dom, args) with
    | _ :: dom, _ :: args -> get_eta_args dom args
    | _, _ -> dom
  in
  (* Save and clear the single-use closure flag so that nested eta_fun calls
     (from processing args) do not inherit it. The saved value is used when
     this eta_fun constructs a partial-application lambda. *)
  let eta_keep_moves = slot.Slot.eta_keep_moves in
  (* Read once: the flag describes this closure, not anything built inside it. *)
  let slot = {slot with Slot.eta_keep_moves = false} in
  match f with
  | Core.Expr.Global ({callee = id; _} as use) ->
    let lowered =
      Calls.lower_call cx ~caller:!Base.Table.current_decl_ref ~slot ?expected_ty env use args
    in
    let plan = lowered.Calls.plan in
    let {
      Calls.instantiated =
        {
          Core_plan.Elaborated_call.call =
            { Core_plan.Elaborated_call.excess = excess_args;
              primary = primary_core_args;
              instances = typeclass_core_args;
              regular = regular_core_args;
              _ } as call;
          params_orig = fn_param_core_tys_orig;
          subst_index_of_orig;
          _
        };
      tvars = tvars;
      instance_promoted = instance_promoted_map;
      _
    } = plan in
    let leading_params = Core_plan.Elaborated_call.leading_params call in
    (* The C++ arguments of a call by name, from the regular arguments in
       declared order (the given ones, then any eta parameters): a declared
       [unit] parameter has no C++ counterpart
       ({!Base.Type_util.declaration_drops_binder}), and Rocq's [unit] argument
       computes nothing worth keeping.  A custom's text takes its arguments by
       position, and a projection reads a field holding a callable value, so
       their lists are left whole. *)
    let passed (l : Cpp_ir.Lowered.Expr.t list) =
      if Base.Table.is_custom id || Base.Table.is_projection id then l
      else
        List.filteri
          (fun i _ ->
            not
              (match Core_plan.Param_pos.nth fn_param_core_tys_orig (Core_plan.Param_pos.of_regular ~leading:leading_params i) with
               | Some t -> Base.Type_util.declaration_drops_binder t
               | None -> false ) )
          l
    in
    (* The callee applied to all but the excess args, where that names no
       local: a function -- a handler [case_] combines -- built from nothing
       the call can change, as Core decided it
       ({!Core_plan.Elaborate.closed_head_call}). *)
    let closed_head =
      (not slot.Slot.building_constant)
        && Core_plan.Elaborate.closed_head_call ~walk:(elaborations cx) ~lex:(current_lexenv cx ()) use args
    in
    let typed_args =
      let slot = if closed_head then {slot with Slot.building_constant = true} else slot in
      with_promoted_var_map cx (instance_promoted_map @ cx.ctx.lexical.promoted_var_map)
        (fun () -> gen_call_args cx ~slot ?expected_ty ~written_by_var:lowered.Calls.written_by_var env id plan)
    in
    let args = List.map (fun (a : Typed.t) -> a.expr) typed_args in
    let ty = lowered.Calls.callee_type
    and tys = lowered.Calls.written
    and all_type_args = Core_plan.Template_application.to_list lowered.Calls.application
    and written_tvar_args = lowered.Calls.written_by_var in
    (* The callee's declared type at the type arguments the call writes: what
       C++ checks the arguments against and returns.  A type argument standing
       for a function type is spelled curried ([Through_tvar]), where the
       value passed was spelled where it was declared. *)
    let live_fn_ty =
      lazy
        (Option.map
           (fun t ->
             let live = Types.cpp_of_core cx env t in
             if Base.Probe.checking () then Calls.check_installed_arity cx id live;
             live )
           (callee_core_type cx id))
    in
    let written_fn_ty =
      let subst i = Core.Scheme.Var.assoc_tvar i written_tvar_args in
      (* An inline custom has no signature its type arguments instantiate:
         its text reads the values as they are ({!Calls.call_result_site}). *)
      if written_tvar_args = [] || is_inline_custom id then None
      else Option.map (Cpp_ir.Types.substitute subst) (Lazy.force live_fn_ty)
    in
    (* The same type with the variables the call leaves to C++ deduced from
       the arguments' types, as C++ deduces them
       ({!Cpp_ir.Types.deduce}): what the call yields, where every variable
       its codomain mentions is written or deduced.  Only typing reads it. *)
    let deduced_fn_ty =
      match Lazy.force live_fn_ty with
      | Some (Cpp_ir.Type.Function (doms, cod) as live)
        when (not (is_inline_custom id)) && List.compare_lengths doms typed_args = 0 ->
        let written i = Core.Scheme.Var.assoc_tvar i written_tvar_args in
        let unknown i = written i = None in
        let deduced =
          List.concat
            (List.map2
               (fun d (a : Typed.t) ->
                 match Cpp_ir.Value_type.arrows a.ty with
                 | Some ar -> Cpp_ir.Types.deduce ~unknown d (Cpp_ir.Arrows.to_type ar)
                 | None -> ( match a.ty with Typed t -> Cpp_ir.Types.deduce ~unknown d t | _ -> [] ) )
               doms typed_args )
        in
        let subst i = match written i with Some t -> Some t | None -> List.assoc_opt i deduced in
        let resolved =
          not
            (Cpp_ir.Types.exists
               (fun (t : Cpp_ir.Lowered.Type.t) ->
                 match t with Variable (Index (i, _)) -> subst i = None | _ -> false )
               cod )
        in
        if resolved then Some (Cpp_ir.Types.substitute subst live) else None
      | _ -> None
    in
    (* Each argument read at its parameter as the call writes it
       ({!Coerce.regroup_crossing}): [pf : pair<fn<R(A, B)>, nat>] passed to
       [myfst<fn<fn<R(B)>(A)>, nat>].  Only where every argument has its own
       parameter to line up with: no erased argument, no erased domain, and
       no receiver -- a method's is read at its struct's own instantiation,
       not at type arguments the call writes. *)
    let args =
      match written_fn_ty with
      | Some (Cpp_ir.Type.Function (doms, _))
        when Unit_plan.Cpp_names.lookup_method_this_pos id = None
             && List.length doms >= List.length args
             && List.length regular_core_args = List.length args
             && not (List.exists (function Core.Expr.Erased_value _ -> true | _ -> false) regular_core_args)
             && not
                  (List.exists
                     (fun t ->
                       Base.Type_util.is_typeclass_type_cpp t || is_cpp_dummy_type t || is_skipped_cpp_type t )
                     doms ) ->
        List.map2
          (fun (core_arg, a) into ->
            let crossed = function
              | Some from -> (
                (* Keep [a] itself when nothing converts: the caller tests
                   whether the crossing converts by physical identity. *)
                match Coerce.regroup_crossing ~from ~into a with
                | Cpp_ir.Expr.Convert (t, _) -> (Convert (t, a) : Cpp_ir.Lowered.Expr.t)
                | _ -> a )
              | None -> a
            in
            (* What the crossing writes depends on the source only through
               whether it converts. *)
            let converts t = crossed t != a in
            crossed (Coerce.value_cpp_type cx ~agree:(fun p l -> converts p = converts l) env core_arg) )
          (List.combine regular_core_args args)
          (List.filteri (fun i _ -> i < List.length args) doms)
      | _ -> args
    in
    (* A class field called with the instance it projects through, where
       that instance was kept and declares the field as a member template:
       the instance's own method, at the type arguments the projection's body
       forwards -- all but the instance's.  The dispatcher is a template
       forwarding to [_tcI0::bind] that repeats its argument passing, which a
       C++ compiler is not sure to see through.  A method erased at
       [std::any] is left to the dispatcher, which does the erasing.  Core
       decides which calls those are ({!Core_plan.Elaborate.member_template_call}). *)
    let cglob =
      match
        ( plan.Calls.instantiated.call.instances,
          plan.Calls.instance_type_args,
          all_type_args )
      with
      | [inst], [Some inst_ty], _ :: method_targs
        when Core_plan.Elaborate.member_template_call ~walk:(elaborations cx) ~lex:(current_lexenv cx ()) use core_args ->
        (Scope (Type_name inst_ty, Base.Common.id_of_global Term id, method_targs) : Cpp_ir.Lowered.Expr.t)
      | _ ->
        mk_cppglob
          ?yields:(Calls.glob_yields cx env id (Base.Core_util.Var_types.apply tys))
          id all_type_args
    in
    (* Check if this is a typeclass instance used as a type (for :: access).
       When all args are consumed (domain and args both empty after filtering),
       return just the type reference, not a function call. This avoids
       generating numOption<numNat, unsigned int>() instead of numOption<numNat,
       unsigned int> for qualified access like ::to_nat. *)
    let id_is_typeclass_instance = ref_returns_typeclass id in
    (* {b Curried excess args.}  When a call site provides more value args
       than the callee's Core type has arrows, the extras are curried onto the
       result: [f(primary_args)(excess_args)].

       This is valid when the callee genuinely returns a function:
       - Its codomain is a type alias ([Core.Type.Global_app]) that may expand to [Core.Type.Arrow]
         (e.g. [State S A = S -> A * S]).
       - Its codomain is a type variable ([Core.Type.Variable]) that, after instantiation
         with the call-site type args [tys], becomes [Core.Type.Arrow] (e.g.
         [fold_right] with [B = nat -> nat]).
       - It is an inlined custom constant (e.g. [fst], [snd]).

       When the codomain is a type variable that instantiates to a
       non-function type (e.g. [div2_rect] with [T1 = R_div2]), the excess
       args come from proof-certificate functions ([Function] vernacular
       [_correct] terms) that are never called at runtime.  We emit an abort
       placeholder for those. *)
    (* The callee's instantiation at this call: the explicit type arguments
       where the site carries them, and otherwise the one its arguments
       imply. *)
    let inst_tys =
      if not (Base.Core_util.Var_types.is_empty tys) then tys
      else
        match find_type_opt id with
        | Some core_ty -> tvar_instantiation id core_ty primary_core_args
        | None -> Base.Core_util.Var_types.empty
    in
    (* The callee's codomain as this call instantiates it. *)
    let instantiated_codomain core_ty =
      let cod = core_codomain core_ty in
      if Base.Core_util.Var_types.is_empty inst_tys then cod else Base.Core_util.Var_types.apply inst_tys cod
    in
    let wrap_excess (base : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
      if excess_args = [] then
        base
      else (
        (* A closed head is built once ({!Cpp_passes.Constants}), not at every
           evaluation of the application: in OCaml it would be a partial
           application, evaluated where the handler is passed rather than at
           every event the handler answers. *)
        let base : Cpp_ir.Lowered.Expr.t =
          match base with
          | Call _ when closed_head ->
            Cpp_ir.Build.call
              (Runtime (Cpp_ir.Crane_rt.Constant (String.lowercase_ascii (Label.to_string (Base.Common.label_of_r id)))))
              [base]
          | _ -> base
        in
        let ret_is_chainable =
          is_inline_custom id
          ||
          match find_type_opt id with
          | Some core_ty ->
            let cod = core_codomain core_ty in
            ( match resolve_meta cod with
            | Core.Type.Global_app _ -> true
            | Core.Type.Arrow _ -> true
            | Core.Type.Unknown -> true
            (* A codomain that applies a variable -- [interp]'s [M R], at
               [M := stateT S m] -- is a function exactly where the variable
               is instantiated at one, which is the same question as for a
               bare variable. *)
            | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; _} | Core.Type.Variable_app _ ->
              (* Type variable: instantiate with the call-site type args to
                 determine if the return type is actually a function.
                 [cod] is already the function's codomain (all arrows
                 stripped), so after substitution we check [cod_inst]
                 directly — NOT [core_codomain cod_inst], which would strip
                 another layer of arrows and reject valid cases like
                 [fold_right] instantiated at [A = nat -> nat].

                 When [tys] is empty (the use wrote no type argument, its
                 types carried as [Core.Expr.Erased_value] in [args] instead),
                 substitution is a no-op and the [Core.Type.Variable] stays unresolved.
                 In this case, chain unconditionally: Rocq's type system
                 guarantees that excess {i value} args (non-[Core.Expr.Erased_value]) can
                 only exist when the return type instantiates to a function.
                 Proof-level excess args are already removed by the
                 [Core.Expr.Erased_value] filter above. *)
              if Base.Core_util.Var_types.is_empty inst_tys then
                true
              else
                let cod_inst = Base.Core_util.Var_types.apply inst_tys cod in
                ( match resolve_meta cod_inst with
                | Core.Type.Arrow _ -> true
                | Core.Type.Global_app _ -> true
                | Core.Type.Erased Core.Erasure_reason.Type_argument -> true
                | Core.Type.Unknown -> true
                | _ -> false )
            | _ -> false )
          | None -> false
        in
        (* The callee hands back a box, so the excess args are applied to a
           [std::any] and have to go through the erased calling convention.
           A result pinned down only by a type index is written [std::any] in
           the declaration however this call site instantiates it, so it
           counts here just as it does in {!gen_expr}'s [Core.Expr.Apply] case. *)
        let cod_is_erased =
          match callee_core_type cx id with
          | Some core_ty ->
            Erasure.core_erases_to_box cx env (instantiated_codomain core_ty)
            || ( match Calls.result_cpp_via_receiver cx env core_ty primary_core_args with
               | Some c -> Erasure.is_boxed_source cx c
               | None -> false )
            || result_is_index_only_tvar core_ty
          | None -> false
        in
        (* The codomain as this call site instantiates it: that is the type
           the excess args are applied to. *)
        let cod_inst =
          match callee_core_type cx id with
          | Some core_ty -> Some (instantiated_codomain core_ty)
          | None -> None
        in
        let cod_site = Calls.call_result_site id in
        (* A codomain that stays curried in C++ -- a [std::function] whose
           result is another [std::function] -- takes only the arguments of
           its own arrow, so applying every excess arg in one call would
           overrun it.  The args go in the groups the type accepts them in. *)
        (* The callee's codomain as the call writes it: its declared type at
           the written type arguments, which is what C++ returns -- [case_]'s
           [T2] written [std::function<std::any(std::any)>] where the Core
           instantiation erased the morphism type. *)
        let written_cod =
          let subst i = Core.Scheme.Var.assoc_tvar i written_tvar_args in
          match
            Option.map
              (fun t -> Cpp_ir.Types.substitute subst (Types.cpp_of_core cx env t))
              (callee_core_type cx id)
          with
          | Some (Cpp_ir.Type.Function (_, c)) -> Some c
          | _ -> None
        in
        (* A group the written type returns boxed, with the rest of the chain
           still to apply: the box holds what an erased morphism produced, the
           result type at an index it never instantiated.  That is the type
           the whole chain is expected to have, as a function of the rest,
           with this declaration's own variables erased -- a handler combined
           by [case_], answering at [std::any] where the enclosing handler
           says [T1].  The chain's value is then read at the expected type. *)
        let boxed_group_target rest_core =
          match (written_cod, expected_ty) with
          | Some (Cpp_ir.Type.Function (_, c)), Some exp
            when Cpp_ir.Types.prints_as_any c && not (Cpp_ir.Types.prints_as_any exp) ->
            let arg_ty a =
              match a with
              | Core.Expr.Bound_variable {index = j; occurrence = occ} ->
                Binders.planned_binder_type_or_derive cx ~use:"argument's type" ~agree:( = ) env j occ
              | _ -> Option.map (Types.cpp_of_core cx env) (Ctor_args.core_ast_type_hint a)
            in
            let rest_tys = List.map arg_ty rest_core in
            if List.for_all Option.has_some rest_tys then
              let scope = get_current_type_vars cx in
              let erase_own =
                Cpp_ir.Types.map (fun (t : Cpp_ir.Lowered.Type.t) ->
                    match t with
                    | Variable tv ->
                      let id = Cpp_ir.Type.variable_spelled tv in
                      if List.exists (Id.equal id) scope then Any else t
                    | t -> t )
              in
              Some (erase_own (Cpp_ir.Type.Function (List.map Option.get rest_tys, exp)))
            else None
          | _ -> None
        in
        (* The groups [excess] goes to the result in, as the codomain [cod]
           takes them.  A codomain written by name -- [stateT nat (stateT
           bool m) A], which is [nat -> stateT bool m (nat * A)] -- takes the
           arguments of the arrows the name stands for, and what is left
           after them may be another such name.  The last group takes
           whatever is left. *)
        let rec excess_groups cod (excess : Cpp_ir.Typed.t list) : Cpp_ir.Lowered.Type.t list list =
          if excess = [] then []
          else
            let cod = Option.map expand_core_fun_alias cod in
            let cod_cpp c = Cpp_ir.Types.spell_arrows cod_site (Types.cpp_of_core cx env c) in
            match Option.map cod_cpp cod with
            | Some (Function (dom, _)) when List.length dom < List.length excess ->
              let n = List.length dom in
              dom :: excess_groups (Option.map (core_drop_arrows n) cod) (List.filteri (fun i _ -> i >= n) excess)
            | _ ->
              [ List.map
                  (fun (a : Cpp_ir.Typed.t) : Cpp_ir.Lowered.Type.t -> match a.ty with Typed t -> t | _ -> Auto)
                  excess ]
        in
        let chain_excess base cod excess =
          let excess = List.map Cpp_ir.Typed.of_node excess in
          match excess_groups cod excess with
          | [] -> base
          | groups -> (Cpp_ir.Typed.apply (Cpp_ir.Typed.typed (Cpp_ir.Arrows.to_type {groups; result = Auto}) base) excess).expr
        in
        (* A domain the codomain spells [std::any] -- the event of a handler
           that [case_] combined at an erased family -- is opened by code that
           erased the value type's parameters as well, and so reads it at the
           all-[std::any] instantiation (see [crane_all_any]).  A generated
           inductive goes in at that instantiation, through its converting
           constructor, rather than at the one this call site knows. *)
        let erase_params_into_boxes excess =
          let doms =
            match Option.map (Types.cpp_of_core cx env) cod_inst with
            | Some (Function (dom, _)) -> dom
            | _ -> []
          in
          List.mapi
            (fun i e ->
              match (List.nth_opt doms i, List.nth_opt excess_args i) with
              | Some d, Some (Core.Expr.Bound_variable {index = j;
                                                        occurrence = occ}) when Cpp_ir.Types.prints_as_any d -> (
                let unfolded =
                  Option.map (fun t ->
                      Convert.strip_ns_global_app (Types.unfold_cpp_typedef cx env t) )
                in
                let is_any (a : Cpp_ir.Lowered.Type.t) = match a with Any -> true | _ -> false in
                (* Read for the inductive, its arity and namespace, and
                   whether every argument is already a box. *)
                let reading t =
                  match unfolded t with
                  | Some (Cpp_ir.Type.Entity_application ((GlobRef.IndRef _ as g), (_ :: _ as args), ns)) ->
                    Some (g, List.length args, ns, List.for_all is_any args)
                  | _ -> None
                in
                match
                  unfolded
                    (Binders.planned_binder_type_or_derive cx ~use:"excess argument"
                       ~agree:(fun p l -> reading p = reading l) env j occ)
                with
                | Some (Cpp_ir.Type.Entity_application ((GlobRef.IndRef _ as g), (_ :: _ as args), ns))
                  when (not (Base.Table.is_custom g))
                       && not (List.for_all is_any args) ->
                  Cpp_passes.Erasure.converting_ctor (Entity_application (g, List.map (fun _ -> Cpp_ir.Type.Any) args, ns)) [e]
                | _ -> e )
              | _ -> e )
            excess
        in
        if ret_is_chainable then
          let excess = List.map (gen_expr cx ~slot env) excess_args in
          if cod_is_erased then
            let applied = Coerce.apply_erased_callee base excess in

            (* Args applied to a box come back as a box; the codomain at this
               call's instantiation is what says what that box holds. *)
            let recovered_at =
              let from_cod =
                Option.map
                  (fun c ->
                    Types.cpp_of_core cx env (core_drop_arrows (List.length excess) c) )
                  cod_inst
              in
              (* The instantiated codomain does not always name a type to
                 recover at -- it may itself be erased, the very reason the
                 application went through the boxed convention.  The position
                 the call sits in then says what the value is. *)
              match from_cod with
              | Some c when Coerce.states_unboxed_target c -> from_cod
              | _ -> expected_ty
            in
            Coerce.unbox_into cx recovered_at applied
          else
            (* A codomain instantiated at a type the call erased -- [resum]'s
               [C a b] at [C := IFun], a category over families -- is a
               callable whose C++ type only template deduction knows, and it
               may hand back a box.  The position says what the value is; the
               tolerant cast passes through one that was never boxed. *)
            let excess = erase_params_into_boxes excess in
            let n_first =
              match written_cod with
              | Some (Cpp_ir.Type.Function (dom, _)) -> List.length dom
              | _ -> List.length excess
            in
            match
              if n_first < List.length excess then
                boxed_group_target (List.filteri (fun i _ -> i >= n_first) excess_args)
              else None
            with
            | Some target ->
              let here = List.filteri (fun i _ -> i < n_first) excess in
              let rest = List.filteri (fun i _ -> i >= n_first) excess in
              let r = Cpp_ir.Build.call (Coerce.unbox_value cx target (Cpp_ir.Build.call base here)) rest in
              ( match expected_ty with
              | Some exp -> Convert (exp, r)
              | None -> r )
            | None ->
            let r = chain_excess base cod_inst excess in
            match (Option.map resolve_meta cod_inst, expected_ty) with
            | Some (Core.Type.Erased Core.Erasure_reason.Type_argument), Some t
              when not (Cpp_ir.Types.prints_as_any t) ->
              Cpp_passes.Erasure.unbox_tolerant t r
            | _ -> r
        else
          Abort ("untranslatable curried proof term", Cpp_build.abort_ty expected_ty) )
    in
    let primary_result : Cpp_ir.Lowered.Expr.t =
      match ty with
      | Function (dom, cod) ->
        (* Filter domain to exclude type class types (they're now template
           params) and erased types.  Proof params like wf witnesses may
           extract as function types containing dummy_type (e.g.
           [Function ([List<T1>], dummy_type)]) rather than plain dummy_type. These
           entries must be removed to match the Core argument list which already
           filters out Core.Expr.Erased_value entries. *)
        (* Only a dummy -- an erased proof or type -- is filtered.  A value
           parameter whose type erases, [e : a T] at an erased family, prints
           as [std::any] and is a parameter all the same: dropping it made a
           call one short look saturated. *)
        let dom =
          List.filter
            (fun t ->
              (not (Base.Type_util.is_typeclass_type_cpp t))
              && (not (is_cpp_dummy_type t))
              && not (is_skipped_cpp_type t) )
            dom
        in
        (* [dom] is the substituted type's, and substitution can erase a
           parameter the declaration still takes -- an argument given at it
           is passed, but has no place in [dom] to be counted against, and
           the call would look saturated one argument early.  Those are
           discounted; see [subst_index_of_orig]. *)
        (* What a partial application is missing is what the declaration
           takes after the given arguments, in the declaration's order.  A
           parameter whose declared type applies a variable is one of them
           even where the substitution erased it -- [fused_trigger]'s event
           [e : F T] at a family [F] erased because it is applied to a section
           variable -- since the application of an erased family is still a
           type of values; it takes the box its type erased to. *)
        let missing_args =
          let from_dom =
            get_eta_args dom
              (List.filteri
                 (fun i _ ->
                   subst_index_of_orig
                     (Core_plan.Param_pos.of_regular ~leading:leading_params i)
                   <> None )
                 args )
          in
          let rec in_declared_order params from_dom =
            match params with
            | [] -> from_dom
            | (o, t) :: rest ->
              let applies_a_variable =
                match resolve_meta t with Core.Type.Variable_app _ -> true | _ -> false
              in
              ( match (subst_index_of_orig o, from_dom) with
              | None, _ when applies_a_variable ->
                Cpp_ir.Type.Any :: in_declared_order rest from_dom
              | None, _ -> in_declared_order rest from_dom
              | Some _, d :: from_dom' -> d :: in_declared_order rest from_dom'
              | Some _, [] -> [] )
          in
          (* The parameters past the arguments the call gives. *)
          let untaken =
            List.filter
              (fun (o, _) ->
                match Core_plan.Param_pos.regular_of ~leading:leading_params o with
                | Some r -> r >= List.length args
                | None -> false )
              (Core_plan.Param_pos.positioned fn_param_core_tys_orig)
          in
          in_declared_order untaken from_dom
        in
        (* When excess args exist (from the Core-level arity split above), do
           NOT eta-expand even if the flattened C++ type has more domain
           elements than Core arguments.  The mismatch occurs when the callee's
           return type is itself a function type (e.g. [fst] returning
           [Obj -> Path<Obj>]): the C++ type conversion merges the
           return-type arrows into the domain, making the domain list longer
           than the Core-level arity.  The excess args will be chained by [wrap_excess]
           below. *)
        (* A mapping that writes no argument placeholder stands for a value,
           not for a call that is short of arguments: it renders as-is, and
           eta-expanding it would state an arity of our own invention.  Its own
           arity is not even knowable here -- the domain a value parameter
           erases to is filtered out of [dom] above, so a dictionary taking an
           erased argument looks one arrow shorter than the parameter it is
           passed as.  A mapping that does write placeholders is a call, and is
           eta-expanded to fill them. *)
        let written_bare =
          args = []
          && ( id_is_typeclass_instance
             || (is_inline_custom id && Calls.inline_custom_arg_arity id = Some 0) )
        in
        if written_bare then cglob
        else if missing_args == [] || excess_args <> [] then
          if is_inline_custom id && args = [] then
            (* Nothing is missing, so there is nothing to fill: the template
               renders with what it was given. *)
            cglob
          else Calls.apply_global cx id cglob (passed args)
        else
          (* Substitute promoted type vars in eta-expanded lambda params. When
             partially applying a function like pick_op<nat_magma>, the domain
             types may contain [Promoted_member carrier], a promoted type var.
             We resolve these to the concrete type from the typeclass instance
             (e.g., unsigned int from nat_magma::carrier). *)
          let missing_args, cod =
            if typeclass_core_args <> [] && missing_args <> [] then
              let subst_map =
                List.concat_map
                  (fun tc_arg ->
                    match tc_arg with
                    | Core.Expr.Global {callee = r; _} ->
                      let bindings =
                        Unit_plan.Context.instance_promoted_types_of (Lowering_state.unit_context cx) r
                      in
                      List.map
                        (fun (var_name, core_ty) ->
                          let cpp_ty =
                            Types.cpp_of_core cx env core_ty
                          in
                          (var_name, cpp_ty) )
                        bindings
                    | _ -> [] )
                  typeclass_core_args
              in
              if subst_map <> [] then
                let rec subst_promoted : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
                  | Promoted_member name ->
                    ( match
                        List.find_opt
                          (fun (vid, _) -> Id.equal vid name)
                          subst_map
                      with
                    | Some (_, concrete) -> concrete
                    | None -> Promoted_member name )
                  | Const t -> Const (subst_promoted t)
                  | Function (d, c) ->
                    Function (List.map subst_promoted d, subst_promoted c)
                  | Shared_pointer t -> Shared_pointer (subst_promoted t)
                  | t -> t
                in
                (List.map subst_promoted missing_args, subst_promoted cod)
              else
                (missing_args, cod)
            else
              (missing_args, cod)
          in
          (* A variable of the callee's the call left free and no caller
             variable spells alike is the eta-lambda's own to bind (see
             [eta_tparams]); unnamed, it would read as an erased one. *)
          let missing_args, cod =
            let name_free =
              Cpp_ir.Types.map (fun (t : Cpp_ir.Lowered.Type.t) ->
                match t with
                | Variable (Index (i, None))
                  when not
                         (List.exists (Id.equal (Base.Common.tvar_id i))
                            cx.ctx.lexical.current_type_vars) ->
                  Variable (Index (i, Some (Base.Common.tvar_id i)))
                | t -> t )
            in
            (List.map name_free missing_args, name_free cod)
          in
          (* The domains the callee's own declaration spells.  [ty] came from
             the Core type {e this call} instantiates, and a higher-kinded class
             parameter is erased there, so a parameter the declaration writes
             [std::optional<T1<std::any>>] arrives as [std::optional<std::any>]
             -- the carrier is simply gone.  It is not gone from the call,
             which has already recovered it into [all_type_args]; and the
             callee's {e uninstantiated} C++ type is where that carrier still
             has a name to be substituted for.  Substituting the explicit
             arguments back into it reconstructs what the declaration says,
             which is the slot each eta parameter has to fit. *)
          let decl_doms, decl_cod =
            (* A phantom position written [void] is one the declaration does
               not use -- [fused_trigger]'s [F], whose only occurrence it
               relaxed to a deduced parameter -- so in a domain it is erased,
               and applied it is the erased type ([void<std::any>] is none). *)
            let subst i =
              match Core.Scheme.Var.assoc_tvar i written_tvar_args with
              | Some Cpp_ir.Type.Void -> Some Cpp_ir.Type.Any
              | t -> t
            in
            let collapse_erased_heads =
              Cpp_ir.Types.map (fun (t : Cpp_ir.Lowered.Type.t) ->
                  match t with Apply (h, args) -> Cpp_ir.Types.apply h args | t -> t )
            in
            match
              Option.map
                (fun t ->
                  collapse_erased_heads
                    (Cpp_ir.Types.substitute subst (Types.cpp_of_core cx env t)) )
                (callee_core_type cx id)
            with
            | Some (Function (doms, dcod)) -> (doms, Some dcod)
            | _ -> ([], None)
          in
          (* The eta parameters fill the callee's {e trailing} domains; the
             arguments the call already has fill the leading ones.  An
             instantiation may have more arrows than the declaration --
             [idp] at [A := nat -> nat -> nat] -- and a parameter before the
             declaration's own domains has no slot there. *)
          let slot_dom i =
            let k = List.length decl_doms - List.length missing_args + i in
            if k < 0 then None else List.nth_opt decl_doms k
          in
          let tvars = get_current_type_vars cx in
          let erased_eta_param (ty : Cpp_ir.Lowered.Type.t) =
            Base.Type_util.has_tany_written ty && not (Cpp_ir.Types.prints_as_any ty)
            && (match ty with Shared_pointer _ | Function _ -> false | _ -> true)
          in
          (* Whether the declaration had anything to say about this call's
             parameters.  It is the same question for the result, so it is
             asked once: a declaration that could not refine a single parameter
             is one whose substitution does not describe this call, and reading
             the result off it would be reading the same wrong thing. *)
          let decl_spoke = ref false in
          let eta_args =
            List.mapi
              (fun i ty ->
                let ty =
                  match slot_dom i with
                  | Some slot ->
                    let refined =
                      Base.Type_util.refine_param_from_slot ~tvars ~slot ty
                    in
                    if refined <> ty then decl_spoke := true;
                    refined
                  | None -> ty
                in
                let wrapped : Cpp_ir.Lowered.Type.t =
                  match ty with
                  | Shared_pointer _ -> Reference (Lvalue, Const ty)
                  (* A parameter erased in part takes whatever instantiation
                     the caller has and is read at this one by
                     [crane_convert] (see crane_fn.h): a slot spelled
                     [std::function<std::optional<box<Nat>>(...)>] cannot
                     call a lambda declared [std::optional<box<std::any>>],
                     because [std::optional]'s conversion between the two
                     is disabled by the aggregate [box<std::any>]. *)
                  | _ when erased_eta_param ty || Types.mentions_unresolved_promoted cx ty ->
                    Reference (Lvalue, Const Auto)
                  | _ -> ty
                in
                (wrapped, Some (eta_param_id i)) )
              missing_args
          in
          let eta_arg_reads =
            List.mapi
              (fun i ty ->
                let ty =
                  match slot_dom i with
                  | Some slot -> Base.Type_util.refine_param_from_slot ~tvars ~slot ty
                  | None -> ty
                in
                (* The callee spells a field this scope cannot -- its own
                   instance resolves [state] -- so converting to the spelling
                   here would convert to the file-scope box; the argument goes
                   through to the callee's own parameter instead. *)
                if erased_eta_param ty && not (Types.mentions_unresolved_promoted cx ty)
                then fun e : Cpp_ir.Lowered.Expr.t -> Convert (ty, e)
                else fun e -> e )
              missing_args
          in
          (* A closure's captures are [const] in its body, so a move of one
             is a copy there and cannot leave the next call a moved-from
             value.  Where the closure is single-use ([eta_keep_moves], from
             an [Core.Expr.Let]) it borrows its scope instead and the moves are the
             enclosing scope's own. *)
          let eta_vars =
            List.mapi
              (fun i _ -> (List.nth eta_arg_reads i) (Local (eta_param_id i)))
              eta_args
          in
          (* The closure may be called many times (it is handed to a fold or
             a map), and Rocq evaluates a partial application's arguments
             once, where it is built.  An argument that computes something
             is therefore bound once outside the closure, which captures
             the result; left in the body it would be computed again on
             every call. *)
          let rec eta_arg_is_cheap (e : Cpp_ir.Lowered.Expr.t) =
            match e with
            | Local _ | Entity _ | Literal _ | Enum_value _
            | Numeral _ | This | Lambda _
            | Call (_, Runtime (Cpp_ir.Crane_rt.Constant _), _) ->
              true
            | Move e | Dereference e | Member (e, _) | Project (e, _, _)
            | Access (_, e, _) | Forward (_, e)
            | Any_cast (_, e) | Tolerant_any_cast (_, e) | Unbox (_, e)
            | Convert (_, e) | Box (_, e) | Erase_callable (_, e)
            | Function_value e ->
              eta_arg_is_cheap e
            | Call
                (_, Entity (_, _, Some {inline = Some {shape = Pair_projection _; _}; _}), [e]) ->
              eta_arg_is_cheap e
            (* A dictionary built from cheap parts -- [ReSum_inr] over a
               handler, say -- costs a few closures, no more than the call
               it feeds.  Bound outside, it is built wherever the closure is,
               including every time a handler sum is formed for an event
               the closure never sees. *)
            | Call (_, Entity (r, _, _), args) when Base.Table.builds_instance r ->
              List.for_all eta_arg_is_cheap args
            | Converting_construct (_, args) -> List.for_all eta_arg_is_cheap args
            | _ -> false
          in
          (* The number of arguments the callee itself takes.  An
             inline-custom template stops at its last [%aN] placeholder:
             arguments past it are dropped when it is rendered, and a
             placeholder with no argument cannot be rendered at all.  A
             function whose codomain is a type variable stops at its Core
             arrows, because its declaration had no way to flatten a
             codomain it could not see -- the extra arrows only appear at
             this call site, where the variable is instantiated at a
             function type. *)
          let callee_arity =
            match Calls.inline_custom_arg_arity id with
            | Some _ as a -> a
            | None -> (
              match find_type_opt id with
              | Some core_ty when Calls.codomain_site core_ty = Cpp_ir.Types.Through_tvar ->
                Some (count_core_value_arrows core_ty)
              | _ -> None )
          in
          (* A call that already fills its callee -- [fold_right compose id
             fs] at [A := nat -> nat] -- is missing only its result's own
             parameter.  Rocq evaluates it once, where it is written, and its
             result is the closure; eta-expanded, the lambda would make the
             whole call again every time it is applied. *)
          let saturated =
            (not (is_inline_custom id))
            && List.length missing_args = 1
            && match callee_arity with Some arity -> List.length args >= arity | None -> false
          in
          if saturated then
            match Cpp_ir.Build.call cglob (passed args) with
            | Call (cs, f, a) -> Call ({cs with occurrence = Some (Core.Global_use.occurrence use)}, f, a)
            | e -> e
          else
          let eta_hoisted = ref [] in
          let args =
            List.mapi
              (fun i a : Cpp_ir.Lowered.Expr.t ->
                if eta_keep_moves || eta_arg_is_cheap a then a
                else begin
                  let id = Id.of_string (Printf.sprintf "_pa%d" i) in
                  eta_hoisted :=
                    (Bind_variable (id, Declare (Auto, None), a) : Cpp_ir.Lowered.Stmt.t) :: !eta_hoisted;
                  Local id
                end )
              args
          in
          let eta_bind_once lam =
            match List.rev !eta_hoisted with
            | [] -> lam
            | decls -> Cpp_ir.Build.iife None (decls @ [Return (Some lam)])
          in
          let call_args = args @ eta_vars in
          (* The result is the callee's, so it is read off the declaration for
             the same reason the parameters are: what the call returns is
             [std::optional<T1<std::any>>], not the [std::optional<std::any>]
             the erased Core type says. *)
          let cod =
            match decl_cod with
            | Some slot when !decl_spoke ->
              Base.Type_util.refine_param_from_slot ~tvars ~slot cod
            (* A result the substitution erased outright has no other
               statement than the declaration's, which is taken whole
               wherever this scope can spell it. *)
            | Some slot when Cpp_ir.Types.prints_as_any cod && Types.names_only_scoped_tvars cx slot
              ->
              slot
            | _ -> cod
          in
          (* The call the lambda makes is the application completed, made of
             the global's use as a saturated one is. *)
          let call =
            let made_of occurrence (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
              match e with
              | Call (cs, f, a) -> Call ({cs with occurrence = Some occurrence}, f, a)
              | e -> e
            in
            match callee_arity with
            | Some arity ->
              (* The eta parameters first finish filling the callee, and only
                 what is left over is applied to its result -- which is a
                 callable, since that is why there were missing arguments to
                 begin with. *)
              let k = max 0 (arity - List.length args) in
              let fill = List.filteri (fun i _ -> i < k) eta_vars in
              let surplus = List.filteri (fun i _ -> i >= k) eta_vars in
              (* A call that fills the callee exactly yields the lambda's
                 result: recorded, so a mapping's [%ret] can name it. *)
              let yields = if surplus = [] && cod <> Void then Some cod else None in
              let filled =
                made_of (Core.Global_use.occurrence use) (Cpp_ir.Build.call ?yields cglob (passed (args @ fill)))
              in
              (* The surplus goes to the result in the groups its spelling
                 takes them in ({!Calls.call_result_site}). *)
              let filled_ty =
                Cpp_ir.Types.spell_arrows (Calls.call_result_site id)
                  (Function (List.map fst (List.filteri (fun i _ -> i >= k) eta_args), cod))
              in
              (Cpp_ir.Typed.apply (Cpp_ir.Typed.typed filled_ty filled) (List.map Cpp_ir.Typed.of_node surplus)).expr
            | None -> made_of (Core.Global_use.occurrence use) (Cpp_ir.Build.call cglob (passed call_args))
          in
          let ret_ty, (body : Cpp_ir.Lowered.Stmt.t list) =
            if cod = Void then
              (* Void-returning function: execute for side effects, then
                 return without a value. *)
              (None, [Expression call; Return None])
            else
              (Some cod, [Return (Some call)])
          in
          (* A type variable the eta-lambda's own signature names and the
             enclosing declaration's head does not is the index the natural
             transformation quantified over.  Eta-expansion is what introduced
             it, so eta-expansion is what has to bind it: written nowhere it
             is a free name, which is how [handle_local_debug]'s index reached
             C++ as a bare [T2] under a head declaring only [T1].

             Binding it is all that is decided here.  Whether it survives as a
             [template <typename>] of the lambda or is erased away is
             {!Cpp_build.mk_lambda}'s call, and it turns on whether a parameter
             deduces it -- which is exactly the difference between an index
             the event type still carries ([memM<T2>]) and one erasure took
             out of it (a [LocalE] that is a plain enum). *)
          let eta_tparams =
            let named =
              List.fold_left
                (fun acc t -> Id.Set.union acc (Cpp_ir.Types.variable_names t))
                Id.Set.empty
                (cod :: List.map fst eta_args)
            in
            Id.Set.elements
              (List.fold_left
                 (fun acc x -> Id.Set.remove x acc)
                 named
                 cx.ctx.lexical.current_type_vars )
          in
          let eta_lambda params ret body ~capture =
            Cpp_build.mk_lambda ~tparams:eta_tparams params ret body ~capture
          in
          (* A use site expecting fewer parameters than the callee takes wants
             a curried closure: the arrows past its arity belong to the
             element type it is generic in, not to the callable itself. *)
          ( match expected_ty with
          | Some (Function (exp_dom, _))
            when exp_dom <> [] && List.length exp_dom < List.length eta_args ->
            let n = List.length exp_dom in
            let outer = List.filteri (fun i _ -> i < n) eta_args in
            let inner = List.filteri (fun i _ -> i >= n) eta_args in
            eta_bind_once
              (Cpp_ir.Build.lambda outer None
                 [ Return
                     (Some
                        (eta_lambda inner ret_ty body
                           ~capture:Stored ) ) ]
                 ~capture:Stored )
          | _ when eta_keep_moves ->
            eta_lambda eta_args ret_ty body ~capture:Runs_in_place
          | _ ->
            (* The arguments are read where the closure is made, and taken
               by move there when the plan moves them.  The bound arguments
               are locals of the scope that builds the closure, which ends
               before the closure is called: it copies them. *)
            eta_bind_once
              ( match eta_lambda eta_args ret_ty body ~capture:Stored with
              | Lambda l as e ->
                let free = Cpp_ir.Variables.free_in_expr e in
                let moved =
                  List.filter
                    (fun x -> List.exists (Id.equal x) free)
                    (moved_names env (Ownership_ir.Region.eta_captures cx.ctx.lexical.move_plan core_args))
                in
                Lambda {l with moved = moved}
              | e -> e ) )
      | _ ->
        if id_is_typeclass_instance && args = [] then
          cglob
        else if is_inline_custom id && args = [] then
          (* Zero-arg inline custom: return the glob directly so the
             template string renders as-is, without an appended (). *)
          cglob
        else
          (* A reference to a global {i value} whose C++ type is not a
             function type (e.g. a state-monad-style [std::function] synonym)
             is a data member, not a nullary function, so it must not be
             called.  Only globals whose declaration really takes no C++
             parameters -- thunks and those whose every parameter is erased --
             get the [()]. *)
          Calls.apply_global cx id cglob (passed args)
    in
    (* Collapse identity inline customs (%a0) at AST level.  This prevents
       unnecessary IIFE wrapping when a void call passes through an identity
       wrapper (e.g. Ceval) and then appears in statement position. *)
    let primary_result =
      match primary_result with
      | Call (_, Entity (_, _, Some ci), [single_arg])
        when (match ci.inline with Some {shape = Identity; _} -> true | _ -> false) ->
        single_arg
      | _ -> primary_result
    in
    (* Wrap pair-accessor inline custom arguments in any_cast when the
       argument's Core type is erased.  E.g. [fst vs] where [vs : std::any]
       generates [any_cast<pair<any,any>>(vs).first] instead of [vs.first].
       This is the inline-custom analog of the scrutinee any_cast in
       [gen_custom_cpp_case]. *)
    let primary_result =
      match primary_result with
      | Call (_, (Entity (n, glob_tys, Some ci) as cglob'), [single_arg])
        when (match ci.inline with
              | Some {shape = Pair_projection _; _} -> true
              | _ -> false) ->
        let arg_core_erased =
          (* A variable is erased when its Core type is, or when the C++ type
             it converts to is [std::any] -- a value-dependent type such as
             [symbols_semty gamma] is only opaque after conversion. *)
          let rel_is_erased ty =
            let ty = resolve_meta ty in
            is_erased_core_type ty
            || Erasure.core_erases_to_box cx env ty
          in
          let rec has_magic = function
            (* A coercion around a local variable says nothing on its own: in
               an instance method the class's associated type has already been
               specialised, so the variable holds the concrete pair.  Judge by
               the variable's type when it is known; a coercion is still the
               only evidence available when it is not. *)
            | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
            | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
            | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} -> (
              match get_env_type_opt cx i with
              | Some ty -> rel_is_erased ty
              | None -> true )
            | Core.Expr.Coerce _ | Core.Expr.Boxed_value _ | Core.Expr.Lambda_group_barrier _ -> true
            | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _}; arguments = args} as node ->
              (* If the callee is itself a pair accessor (.first/.second) and
                 its product arg was coerced, result is also std::any *)
              let is_pair_accessor =
                match Base.Table.find_custom_opt r with
                | Some s -> (
                  match Cpp_ir.Foreign.shape_of_text s with
                  | Pair_projection _ -> true
                  | _ -> false )
                | None -> false
              in
              if is_pair_accessor then
                let inner_args =
                  List.filter (fun x -> match x with Core.Expr.Erased_value _ -> false | _ -> true) args
                in
                List.exists has_magic inner_args
              else
                Erasure.glob_declared_cod_erases cx r
                (* A declaration that leaves its result a type variable says
                   nothing on its own; the type this call instantiates it to
                   does. *)
                || ( match infer_core_body_type node with
                   | Some t -> Erasure.is_boxed_source cx (Types.cpp_of_core cx env t)
                   | None -> false )
            | Core.Expr.Global {callee = r; _} -> Erasure.glob_declared_cod_erases cx r
            | Core.Expr.Bound_variable {index = i; _} -> (
              match get_env_type_opt cx i with
              | Some ty -> rel_is_erased ty
              | None -> false )
            | _ -> false
          in
          if List.length regular_core_args > 0 then
            has_magic (List.nth regular_core_args 0)
          else false
        in
        if arg_core_erased then
          let prod_g_opt =
            (* The first argument the C++ call passes: erased domains carry no
               value, so they are not it. *)
            let first_dom =
              try
                match core_value_domains (Base.Table.find_type n) with
                | t :: _ -> Some (resolve_meta t)
                | [] -> None
              with Not_found -> None
            in
            match first_dom with
            | Some (Core.Type.Global_app {head = g; _}) when is_prod_global g -> Some g
            | _ -> None
          in
          ( match prod_g_opt, single_arg with
          | _, Any_cast (Entity_application (g, cast_args, _), _)
            when is_prod_global g && cast_args <> []
                 && List.for_all Cpp_ir.Types.prints_as_any cast_args ->
            (* The argument arrived already recovered from its box, and at the
               erased shape [pair<any, any>].  Its components are boxes too, so
               the accessor's result needs the same recovery at the use site as
               when this branch inserts the cast itself --
               {!Erasure.yields_boxed_component} recognises both shapes. *)
            primary_result
          | _, Any_cast _ -> primary_result
          | Some g, _ when (match glob_tys with
                            | [_; _] ->
                              not (List.exists Base.Type_util.has_tany_in_type
                                     glob_tys)
                            | _ -> false) ->
            (* The accessor's own type arguments name both components
               concretely, so the box can be opened at that very shape --
               tolerantly, because a producer that deep-erased stored
               [pair<any,any>], which [crane_any_cast] recovers component by
               component.  What comes out is concrete, so the accessor's
               result needs no further recovery. *)
            Cpp_ir.Build.call cglob'
              [Cpp_passes.Erasure.unbox_tolerant (Entity_application (g, glob_tys, [])) single_arg]
          | Some g, _ ->
            (* Tolerantly: the Core type says the argument is a box, but a
               producer that could name the pair's shape may have emitted the
               [pair<any, any>] itself rather than a box around it.
               [crane_any_cast] accepts both -- it opens a box and passes a
               pair already in hand through -- where a plain [any_cast] would
               throw on the latter. *)
            Cpp_ir.Build.call cglob'
              [ Cpp_passes.Erasure.unbox_tolerant (Entity_application (g, [Any; Any], [])) single_arg ]
          | None, _ -> primary_result )
        else
          primary_result
      | _ -> primary_result
    in
    let result = wrap_excess primary_result in
    (* A saturated call yields its callee's declared codomain at the type
       arguments it writes: what C++ instantiates, which the Core
       instantiation may have erased ([ReSum_inl] at [ReSum<erased, erased>]
       where the call names the concrete events).  Read at the type expected
       of it where the two differ only in how their arrows are grouped
       ({!Coerce.regroup_crossing}): [wrap<fn<fn<R(B)>(A)>>(f)] stored as a
       [list (A -> B -> R)]. *)
    ( match written_fn_ty with
    | Some (Cpp_ir.Type.Function (doms, written_cod))
      when excess_args = [] && List.length doms = List.length args -> (
      let crossed =
        match expected_ty with
        | Some into -> (
          match Coerce.regroup_crossing ~from:written_cod ~into result with
          | Cpp_ir.Expr.Convert (t, _) -> Some (Cpp_ir.Expr.Convert (t, result) : Cpp_ir.Lowered.Expr.t)
          | _ -> None )
        | None -> None
      in
      let cod = match deduced_fn_ty with Some (Function (_, cod)) -> cod | _ -> written_cod in
      match (crossed, result) with
      | Some c, _ -> Typed.of_node c
      | None, Call _ -> Typed.typed cod result
      | None, _ -> Typed.untyped result )
    | _ -> (
      match (deduced_fn_ty, result) with
      | Some (Function (doms, cod)), Call _ when excess_args = [] && List.length doms = List.length args ->
        Typed.typed cod result
      | _ -> Typed.untyped result ) )
  | _ -> Typed.untyped @@
    (* Non-global callee (e.g., a local variable from Core.Expr.Bound_variable). Filter out Core.Expr.Erased_value
       args — these are erased type/prop parameters that have no runtime
       representation. Unlike the Core.Expr.Global case above, there is no use to
       instantiate here; we only need to drop value-level dummies. *)
    let args =
      List.filter
        (fun x ->
          match x with
          | Core.Expr.Erased_value _ -> false
          | _ -> true )
        args
    in
    (* A class-typed argument is not a value: the concept is met by a type, and
       the method the callee projects declares it as a template parameter.  It
       leaves the argument list for the callee's explicit template arguments,
       which is the only place that parameter can be given. *)
    let tc_args, _, args = Calls.split_instance_args ~lex:(current_lexenv cx ()) args in
    let gen_callee () : Cpp_ir.Lowered.Expr.t =
      match (tc_args, gen_expr cx env f) with
      | [], e -> e
      | _, Scope (b, id, tys) ->
        Scope (b, id, tys @ List.filter_map (fun a -> Calls.core_arg_to_template_type cx env a) tc_args)
      | _, e -> e
    in
    (* The callee's own function type, with an alias standing for one expanded
       -- a single-method class is its method, so [Iter M] {e is} the arrow the
       call goes through. *)
    let erased_callee =
      match f with
      | Core.Expr.Bound_variable {index = i; _}
      | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
      | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} -> erased_member cx i
      | _ -> false
    in
    let callee_fun_core_ty =
      match f with
        | Core.Expr.Global ({callee = r; _} as use)
          when not (Base.Core_util.Var_types.is_empty (Base.Core_util.written_type_args use)) ->
          (match find_type_opt r with
           | Some ty -> Some (Base.Core_util.instantiate_written ~reader:"callee_fun_core_ty" use ty)
           | None -> infer_core_body_type f)
        | _ ->
          ( match infer_core_body_type f with
          | Some ty -> Some ty
          | None ->
            (* A local binder typed by name ([c : church]) shows no arrows in
               the term, so its parameter types can only come from the type the
               environment recorded at the binding site.  Only an alias is
               taken: any other binder either carries its arrows in the term or
               is generalised into a deduced callable, which takes each
               argument at the type the argument already has. *)
            ( match f with
            (* A member of a group recursing at a ground instance takes its
               arguments adapted to its erased parameters
               ({!erased_member_types}). *)
            | Core.Expr.Bound_variable {index = i; _}
            | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
            | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
            | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} when erased_callee ->
              get_env_type_opt cx i
            | Core.Expr.Bound_variable {index = i; _}
            | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
            | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
            | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} -> (
              match get_env_type_opt cx i with
              | Some (Core.Type.Global_app {head = GlobRef.ConstRef _; _} as ty) -> (
                match expand_core_fun_alias ty with
                | Core.Type.Arrow _ as expanded -> Some expanded
                | _ -> None )
              | _ -> None )
            | _ -> None ) )
    in
    let callee_param_tys =
      (* Erased and class-typed domains take no argument slot, so neither
         takes a place in the list this indexes [args] by. *)
      let rec extract_params = function
        | Core.Type.Arrow {parameter = t; result = rest} ->
          ( match resolve_meta t with
          | Core.Type.Erased _ -> extract_params rest
          | t when Base.Table.is_typeclass_type t -> extract_params rest
          | t -> t :: extract_params rest )
        | Core.Type.Meta {contents = Some t} -> extract_params t
        | _ -> []
      in
      match callee_fun_core_ty with Some fty -> extract_params fty | None -> []
    in
    let callee_rel_idx = match f with
      | Core.Expr.Bound_variable {index = i; _}
      | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
      | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} -> Some i
      | _ -> None
    in
    let callee_env_ty =
      match callee_rel_idx with
      | Some i -> (try Some (get_env_type cx i) with _ -> None)
      | None -> None
    in
    let callee_cpp_erased =
      match f with
      | Core.Expr.Bound_variable {index = i; occurrence = occ}
      | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; occurrence = occ}; _}
      | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; occurrence = occ}; _}
      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; occurrence = occ}; _} ->
        Binders.read_is_boxed cx i occ
      | _ -> false
    in
    (* A pattern binder whose definition-site field type is a type variable
       still has a concrete C++ type when the scrutinee instantiates that
       variable concretely — [populate_erased_field_env] recorded it in
       [cpp_binder_types] at that concrete type, and the plan does not box
       it ({!Binders.read_is_boxed}).
       Its erased Core type must not be taken at face value here, or a perfectly
       concrete [std::function<uint64_t(uint64_t)>] field gets wrapped in an
       [any_cast] that does not compile. *)
    let callee_known_concrete =
      match callee_rel_idx with
      | Some i when not callee_cpp_erased ->
        ( match Binders.pattern_binder_type cx i with
        | Some t -> not (Types.resolves_to_any_type cx t)
        | None ->
          (* Likewise for a parameter of the enclosing function: the ambient
             environment may still spell its type as the class/section type
             variable it was abstracted over, while the declaration this body
             belongs to (e.g. a typeclass instance at a function type) pinned
             it to a concrete C++ signature. *)
          ( match parameter_type cx env i with
          | Some t ->
            (not (is_core_erased_ty t))
            && not
                 (Types.resolves_to_any_type cx
                    (Types.cpp_ir_of_core_type cx env
                       (get_current_type_vars cx)
                       t ) )
          | None -> false ) )
      | _ -> false
    in
    (* A callee is only callable through the canonical adapter when nothing
       with a C++ call operator is left of its type -- which is what
       [std::any] means here.  The Core type may say so outright ([Core.Type.Erased],
       [Core.Type.Unknown], a bare [Core.Type.Variable]) or only once converted: a type-level
       [Fixpoint] applied to an argument is a perfectly concrete [Core.Type.Global_app] in
       Core and still lands on a [using sem = std::any] alias in C++. *)
    let erases_to_any ty =
      is_core_erased_ty ty
      || Erasure.core_erases_to_box cx env ty
    in
    let callee_is_bare_any =
      callee_cpp_erased
      || ( (not callee_known_concrete)
         &&
         match callee_env_ty with
         | Some ty -> erases_to_any ty
         | None -> false )
      (* Not a local binder: the callee's own inferred type decides. *)
      || ( callee_rel_idx = None
         &&
         match infer_core_body_type (strip_magic f) with
         | Some t -> erases_to_any t
         | None -> false )
    in
    let callee_has_erased_params =
      callee_is_bare_any ||
      (match callee_env_ty with
      | Some (Core.Type.Arrow {parameter = param; _}) -> is_core_erased_ty param
      | _ -> false) ||
      (match callee_rel_idx with
       | Some i ->
         (match Binders.pattern_binder_type cx i with
          | Some (Function (params, _)) -> List.exists (fun (p : Cpp_ir.Lowered.Type.t) -> p = Any) params
          | _ -> false)
       | None -> false)
    in
    (* [has_unresolved_boxed_arg]: set when an argument is statically known to
       be boxed as [std::any] ({!Binders.read_is_boxed}) but the callee's parameter
       type at this position can't be resolved to a concrete C++ type (it is
       itself abstract/erased, e.g. a value-dependent type scheme like
       [S.sem a]).  This happens when the callee is a genuinely-concrete
       function only at C++ template instantiation time (e.g. a functor
       parameter instantiated with a concrete inlined function) — the OCaml
       side cannot know the concrete type to [any_cast] to.  Such calls are
       routed through the [crane_call_erased] runtime helper instead of a
       direct call, so the concrete parameter types can be recovered via
       [std::function] CTAD once C++ instantiates the template. *)
    let has_unresolved_boxed_arg = ref false in
    let arg_slot =
      if callee_has_erased_params then Slot.into_box Var_box slot else slot
    in
    (* The callee's declared domain at an argument's position, where the
       binding site recorded a declaration: a lambda is written against it,
       curried as it says ([fun a _ => k a] for an [A -> cont R B]).  Not one
       with an erased position, which says less than the lambda's own
       binders -- a handler the callee takes polymorphically is a function
       object, not the erased signature. *)
    let declared_dom i =
      match
        match f with
        | Core.Expr.Bound_variable {index = j; occurrence = occ}
        | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = j; occurrence = occ}; _}
        | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = j; occurrence = occ}; _}
        | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = j; occurrence = occ}; _} ->
          let respelled = Option.map Types.default_tvar_names in
          respelled
            (Binders.planned_binder_type cx ~use:"declared domain"
               ~agree:(fun p l -> respelled p = respelled l) j occ)
        | _ -> None
      with
      | Some (Cpp_ir.Type.Function (dom, _)) -> (
        match List.nth_opt dom i with
        | Some t when not (Cpp_ir.Types.exists Cpp_ir.Types.prints_as_any t) -> Some t
        | _ -> None )
      | _ -> None
    in
    (* The Core type of the callee's parameter at an argument's position:
       the callee's own where the term shows it, else, for a local binder,
       the type its binding site recorded.  Only a type that states every
       part: an erased one says less than the argument's annotation. *)
    let declared_core_dom i =
      let params =
        match (callee_param_tys, f) with
        | (_ :: _ as l), _ -> l
        | [], (Core.Expr.Bound_variable {index = j; _}
              | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = j; _}; _}
              | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = j; _}; _}
              | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = j; _}; _}) ->
          let rec params = function
            | Core.Type.Arrow {parameter = t; result = rest} -> (
              match resolve_meta t with
              | Core.Type.Erased _ -> params rest
              | t when Base.Table.is_typeclass_type t -> params rest
              | t -> t :: params rest )
            | Core.Type.Meta {contents = Some t} -> params t
            | _ -> []
          in
          (match get_env_type_opt cx j with Some t -> params t | None -> [])
        | [], _ -> []
      in
      match List.nth_opt params i with
      | Some t when not (core_type_contains_erased t) -> Some t
      | _ -> arg_slot.Slot.expected_core_ty
    in
    let args =
      List.mapi (fun i x ->
      let expr =
        match x with
        | e when Monadic.core_value_is_void_call cx e ->
          Monadic.wrap_void_call_as_value (gen_expr cx ~slot:arg_slot env x)
        (* A lambda is written against the parameter's Core type as well
           as its C++ one: the binders a flat parameter takes that the term
           does not write become its own ({!Lambda.gen_lambda}), so that it
           takes them as the parameter does.  Not a function type with an
           erased part -- a rank-2 handler's quantifier -- which says less
           than the lambda's own binders. *)
        | Core.Expr.Lambda _ ->
          let expected_core_ty =
            match declared_core_dom i with
            | Some t when not (core_type_contains_erased ~in_arrows:true t) -> Some t
            | _ -> None
          in
          gen_expr cx ?expected_ty:(declared_dom i) ~slot:{arg_slot with Slot.expected_core_ty} env x
        | Core.Expr.Coerce _ | Core.Expr.Boxed_value _ | Core.Expr.Lambda_group_barrier _ ->
          let expected = Types.param_expected_cpp_ty cx env callee_param_tys i in
          gen_expr cx ?expected_ty:expected ~slot:arg_slot env x
        | Core.Expr.Bound_variable {index = j; occurrence = occ} when Binders.read_is_boxed cx j occ ->
          let inner = gen_expr cx ~slot:arg_slot env x in
          let expected = Types.param_expected_cpp_ty cx env callee_param_tys i in
          ( match expected with
            | Some ty ->
              Cpp_passes.Erasure.unbox (Erasure.erase_type_args_to_any ty) inner
            | None ->
              has_unresolved_boxed_arg := true;
              inner )
        (* A value built anywhere in the argument -- at its top, in a
           branch of a match or a let's body, under another constructor --
           is spelled there for the first time, and its annotation may say
           less than the parameter it is passed to: a [None] whose payload
           type extraction left open prints as [std::optional<crane::obj>].
           The parameter's Core type says, and the slot, which every form
           hands on to the positions whose value is the argument's, refines
           the erased parts by it. *)
        | _ -> gen_expr cx ~slot:{arg_slot with Slot.expected_core_ty = declared_core_dom i} env x
      in
      match List.nth_opt callee_param_tys i with
      | Some param_ty when erased_callee -> adapt_to_erased_param cx env param_ty x expr
      | Some param_ty -> Coerce.erase_fn_arg_for_param cx env param_ty x expr
      | None -> expr) args
    in
    (* Detect over-application: when a local variable's C++ type has fewer
       value-domain arrows than the number of Core arguments, the call must be split
       into a primary call and a chained application of excess args. Example: [f
       : A -> State S B] applied as [f(a, s')] becomes [f(a)(s')]. *)
    let n_value_dom =
      let rel_idx_f = match f with
        | Core.Expr.Bound_variable {index = i; occurrence = occ}
        | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; occurrence = occ}; _}
        | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; occurrence = occ}; _}
        | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; occurrence = occ}; _} ->
          Some (i, occ)
        | _ -> None
      in
      match rel_idx_f with
      | Some (i, occ) ->
        ( match get_env_type_opt cx i with
          | None -> List.length args
          | Some ty ->
            let n = count_core_value_arrows ty in
            (* The declaration is what says how the arrows are taken.  A
               parameter the class declares as [A -> m B], whose [m] this
               instance fixes at something itself arrow-shaped, has one domain
               in C++ and two arrows in Core; flattened, the call hands both at
               once to a callable that takes one.  Where the region's plan
               gives the binder a function type -- a method's parameter at
               the type its head declares it -- that is the answer, but only
               where it takes {e fewer}, since a declaration with more
               domains is the under-application the Core count already
               handles and a re-derived type is not a declaration. *)
            let declared = function
              | Some (Cpp_ir.Type.Function (dom, _)) when List.length dom < n -> List.length dom
              | _ -> n
            in
            let n =
              declared
                (Binders.planned_binder_type cx ~use:"call arity"
                   ~agree:(fun p l -> Int.equal (declared p) (declared l))
                   i occ )
            in
            if n < List.length args && Calls.codomain_site ty = Cpp_ir.Types.Through_tvar then
              List.length args
            else n )
      | None -> List.length args
    in
    (* The callee's Core type, from its binder: its first [k] value
       domains, and what it returns past them. *)
    let binder_core_type =
      match f with
      | Core.Expr.Bound_variable {index = i; _}
      | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
      | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} ->
        get_env_type_opt cx i
      | _ -> None
    in
    let rec value_domains k : Core.Type.t -> Core.Type.t list * Core.Type.t = function
      | Core.Type.Arrow {parameter = t; result = rest} when k > 0 -> (
        match resolve_meta t with
        | Core.Type.Erased _ -> value_domains k rest
        | t ->
          let ds, r = value_domains (k - 1) rest in
          (t :: ds, r) )
      | Core.Type.Meta {contents = Some t} -> value_domains k t
      | ty -> ([], ty)
    in
    (* The callee typed from its binder: one group of its first [k] value
       domains. *)
    let callee_typed k core_ty =
      let doms, rest = value_domains k core_ty in
      let conv = Types.cpp_of_core cx env in
      Cpp_ir.Typed.typed (Function (List.map conv doms, conv rest)) (gen_callee ())
    in
    let n_args = List.length args in
    (* Lifting every argument onto the template list still leaves a call. *)
    if n_args = 0 && tc_args = [] then
      (* All args were erased (Core.Expr.Erased_value): no function call, just the
         expression itself.  This arises when erased proof arguments
         (e.g. [le n 0] in [Function]-generated [_rect] bodies) are
         applied to a local variable — the proofs are filtered out,
         leaving an empty arg list.  Generating [f()] would be wrong
         because the C++ type has no 0-arg overload. *)
      gen_callee ()
    else if n_args < n_value_dom && n_value_dom > 0 then
      (* Under-application (partial application due to proof erasure).
         The callee expects [n_value_dom] args but only [n_args] are
         provided — the rest were erased proofs in the same
         [Core.Expr.Apply] that have been filtered out.

         Generate a lambda wrapper that captures the provided args and
         forwards them along with fresh parameters for the remaining
         args.  E.g., [f2(n1)] where [f2 : (nat, T1) -> T1] becomes:
         [[&](T1 _pa0) { return f2(n1, _pa0); }]. *)
      match binder_core_type with
      | Some core_ty when List.length (fst (value_domains max_int core_ty)) > n_args ->
        (* The closure over the rest of the callee's group, its parameters
           [_pa]; what the call reads, the function included, is read where
           the closure is made, and taken by move there when the plan moves
           it. *)
        ( match (Cpp_ir.Typed.apply ~prefix:"_pa" (callee_typed max_int core_ty) (List.map Cpp_ir.Typed.of_node args)).expr with
          | Lambda l ->
            Lambda
              {l with moved = moved_names env (Ownership_ir.Region.eta_captures cx.ctx.lexical.move_plan (f :: core_args))}
          | e -> e )
      | _ -> Cpp_ir.Build.call (gen_callee ()) args
    else if n_args > n_value_dom && n_value_dom > 0 then
      (* Over-application: the callee's declared group, then the excess
         applied to its result. *)
      let callee =
        match binder_core_type with
        | Some core_ty -> callee_typed n_value_dom core_ty
        | None -> Cpp_ir.Typed.untyped (gen_callee ())
      in
      (Cpp_ir.Typed.apply callee (List.map Cpp_ir.Typed.of_node args)).expr
    else
      (* When the callee is a local variable whose Core type is a bare type
         variable (Core.Type.Variable/Core.Type.Unknown), its C++ type is std::any.  std::any
         is not callable, so we must wrap it with std::any_cast to recover the
         std::function type before calling.  Both arg and return types
         default to std::any since the original types are erased.
         The coercion wrapper is transparent — peel it to find the Core.Expr.Bound_variable. *)
      let callee_expr = gen_callee () in
      (* Check whether this call returns [std::any] (erased type) but the
         enclosing function expects a concrete type, requiring an
         [std::any_cast<T>] wrapper.  See [core_codomain_erases_to_any].
         Two callee forms are handled:
         - [Core.Expr.Match] single-branch record projection whose field type has a
           higher-rank codomain (e.g. [apply : forall A, A -> A] stored as
           [std::function<std::any(std::any)>]).
         - [Core.Expr.Bound_variable] higher-rank callback whose env-type has a [Core.Type.Variable] codomain
           guarded by [Core.Type.Erased] (e.g. [f : forall A, A -> A]). *)
      let result =
        if !has_unresolved_boxed_arg && not callee_is_bare_any then begin
          (Tolerant_call (callee_expr, args) : Cpp_ir.Lowered.Expr.t)
        end
        else if callee_is_bare_any then
          Coerce.apply_erased_curried callee_expr args
        else Cpp_ir.Build.call callee_expr args
      in
      let n = n_args in
      let erased_cod =
        (* A callee recovered from a bare [std::any] is called through the
           canonical [std::function<std::any(std::any...)>] adapter, so its
           result is a [std::any] no matter what the Core type says. *)
        callee_is_bare_any
        ||
        match f with
        | Core.Expr.Match {scrutinee_type = case_ty; branches = pv; _} when Array.length pv = 1 ->
          let {Core.Match.Branch.binders = binds; body = br_body; _} = pv.(0) in
          let n_binds = List.length binds in
          let proj_idx =
            match br_body with
            | Core.Expr.Bound_variable {index = i; _} when i >= 1 && i <= n_binds -> Some (n_binds - i)
            | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
            | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
            | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _}
              when i >= 1 && i <= n_binds ->
              Some (n_binds - i)
            | _ -> None
          in
          ( match proj_idx with
          | Some idx ->
            ( match case_ty with
            | Core.Type.Global_app {head = r; _} ->
              let all_ft = Base.Table.record_field_types r in
              let non_erased = filter_value_types all_ft in
              ( try core_codomain_erases_to_any n (List.nth non_erased idx)
                with _ -> false )
            | _ -> false )
          | None -> false )
        | Core.Expr.Bound_variable {index = i; _} ->
          (match get_env_type_opt cx i with Some ty -> core_codomain_erases_to_any n ty | None -> false)
        | _ -> false
      in
      Coerce.recover_boxed_result cx ~boxed:erased_cod ~expected:expected_ty result
      |> Coerce.recover_carrier_result ~fun_ty:callee_fun_core_ty ~n_args:n
           ~want:(Coerce.position_cpp_ty cx expected_ty)

(** The dictionary of a singleton class, the variable [i] read at [occ],
    applied to [args]: the body of the class's projection, which calls the
    method on the instance -- a template parameter, so a static member -- at
    the method's own type variables. *)
let gen_singleton_dictionary_call cx env ~i ~occ ~args : Cpp_ir.Typed.t =
  let inst, class_ref, method_ref = Option.get (singleton_call cx env i occ) in
  (* What the method returns: its declared type at the dictionary's
     carrier, its own variables the projection's. *)
  let codomain =
    match (Base.Table.find_type method_ref, Option.map resolve_meta (get_env_type_opt cx i)) with
    | exception Not_found -> None
    | ty, Some (Core.Type.Global_app {type_arguments = [carrier]; _}) ->
      Some (core_codomain (Core_plan.Query.subst_dict_carrier carrier ty))
    | ty, _ -> Some (core_codomain ty)
  in
  Cpp_ir.Typed.v ~ty:(Typed_checks.core_value_type cx env codomain) @@
  let ipv = List.length (Base.Table.get_ind_ip_vars class_ref) in
  let n_own = Base.Type_util.method_tvar_count class_ref (Base.Table.find_type method_ref) in
  let tvars = get_current_type_vars cx in
  let targs =
    List.init n_own (fun k ->
        Types.cpp_ir_of_core_type cx env tvars (Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                                                         variable = ipv + 1 + k}))
  in
  let value_args = List.filter (function Core.Expr.Erased_value _ -> false | _ -> true) args in
  Cpp_ir.Build.call
    (Scope (Local inst, Base.Common.id_of_global Term method_ref, targs))
    (List.map (gen_expr cx env) value_args)

(** A class field projected through the instance [use] applied to [args]
    names, as Core decided it ({!Core_plan.Elaborate.static_projection_call}); a
    projection missing arguments is eta-expanded over them first. *)
let gen_instance_projection cx ~expected_ty ~slot env ~use ~args : Cpp_ir.Typed.t =
  let projection =
    Option.get (Core_plan.Elaborate.static_projection_call ~walk:(elaborations cx) ~lex:(current_lexenv cx ()) use args) in
  match projection.missing with
  | [] ->
    Cpp_ir.Typed.v
      ~ty:(Typed_checks.core_value_type cx env projection.codomain)
      (project_through_instance cx env use args projection)
  | missing ->
    let k = List.length missing in
    let call =
      Core.Expr.Apply {callee = Core.Expr.Global use;
                       arguments = List.map (Base.Core_util.ast_lift k) args
                         @ List.init k (fun i -> Core.Expr.fresh_rel (k - i))}
    in
    Knot.gen_expr_typed cx ?expected_ty ~slot env
      (Base.Core_util.named_lams
         (List.rev (List.mapi (fun i t -> (Core.Binder_name.Source (Id.of_string ("a" ^ string_of_int i)), t)) missing))
         call )

(** The application of [f] to [args] that no special form claimed: a
    call, partial or saturated ({!eta_fun}), its result recovered from a box
    where only a type index pins it down, and the call node recording its
    signature. *)
let gen_application cx ~expected_ty ~slot env (f : Core.Expr.t) (args : Core.Expr.t list) : Typed.t =
  (* A partial application is a callable this position may expect at a
     different currying than the callee's own arrows give it, so the slot's
     type travels with it. *)
  let call = eta_fun cx ?expected_ty ~slot env f args in
  let result = call.expr in
  (* A callee whose result is only pinned down by a type index hands back a
     [std::any] (see {!result_is_index_only_tvar}); recover it at the type
     this position expects. *)
  let callee_ty =
    match f with
    | Core.Expr.Global {callee = r; _} -> callee_core_type cx r
    | Core.Expr.Bound_variable {index = i; _} -> get_env_type_opt cx i
    | _ -> None
  in
  (* The same type, at the instantiation this call uses: what the call
     yields is the codomain of *that*, not of the general scheme. *)
  let callee_ty_inst =
    match (f, callee_ty) with
    | Core.Expr.Global use, Some ty ->
      let value_args =
        List.filter (function Core.Expr.Erased_value _ -> false | _ -> true) args
      in
      Some (Calls.instantiate_use_at_call cx use value_args ty)
    | _ -> callee_ty
  in
  (* A callee typed by a function alias ([church]) hands back whatever the
     alias's codomain erased to; the alias is the only place that says so,
     since the term itself carries no arrows. *)
  let alias_result_is_boxed ty =
    match ty with
    | Core.Type.Global_app {head = GlobRef.ConstRef _; _} ->
      ( match expand_core_fun_alias ty with
      | Core.Type.Arrow _ as expanded ->
        ( match core_codomain expanded with
        | Core.Type.Variable _ | Core.Type.Unknown -> true
        | _ -> false )
      | _ -> false )
    | _ -> false
  in
  (* A binder whose declared C++ type boxes its result -- a rank-2 parameter
     typed [std::function<std::any(std::any)>], say -- hands back a box
     however the term's Core type reads.  The assignment made where the binder
     was bound is the authority on that; only a saturated call reaches the
     codomain it names. *)
  let binder_result_is_boxed =
    match f with
    | Core.Expr.Bound_variable {index = i; occurrence = occ} ->
      let n_runtime =
        List.length (List.filter (fun a -> not (Base.Core_util.is_erased_value (strip_magic a))) args)
      in
      let boxes t =
        match Option.map (fun t -> Types.unfold_cpp_typedef cx env (strip_cpp_ref_const t)) t with
        | Some (Cpp_ir.Type.Function (doms, cod)) -> Cpp_ir.Types.prints_as_any cod && List.length doms = n_runtime
        | _ -> false
      in
      boxes
        (Binders.planned_binder_type_or_derive cx ~use:"callee result" ~agree:(fun p l -> boxes p = boxes l)
           env i occ)
    | _ -> false
  in
  (* Nor can a global whose declaration boxed its result -- [id] declared
     at [crane::obj] -- hand back anything else, however this call
     instantiates it. *)
  let declared_result_is_boxed =
    match f with Core.Expr.Global {callee = r; _} -> Erasure.glob_declared_cod_erases cx r | _ -> false
  in
  let recovered =
    if
      binder_result_is_boxed || declared_result_is_boxed
      || ( match callee_ty with
         | Some ty -> result_is_index_only_tvar ty || alias_result_is_boxed ty
         | None -> false )
    then Coerce.unbox_into cx expected_ty result
    else result
  in
  (* A call of what [f] names is made of this application, which the
     recursion plan knows by its head: a global's use, or the read of a
     local function -- read as it is, or through the cast unboxing what
     it returns. *)
  let made_of_application (call : Cpp_ir.Lowered.Expr.t) =
    match (f, call) with
    | Core.Expr.Global use, Call (_, Entity (r, _, _), _) when Base.Common.globref_equal r use.callee ->
      made_of (Core.Global_use.occurrence use) call
    | Core.Expr.Bound_variable {occurrence = occ; _}, Call (_, Local _, _) -> made_of occ call
    | _ -> call
  in
  let built : Cpp_ir.Lowered.Expr.t =
    let written = match (call.ty, recovered == result) with Typed t, true -> Some t | _ -> None in
    match Calls.record_call_sig ?written cx env callee_ty_inst recovered with
    | Any_cast (ty, call) -> Any_cast (ty, made_of_application call)
    | result -> made_of_application result
  in
  (* The call's own type, where {!eta_fun} typed it and nothing recovered
     it from a box since; an action of a sequential monad yields its
     result whatever the call's type ({!Typed_checks.of_built}). *)
  let e : Core.Expr.t = Apply {callee = f; arguments = args} in
  if recovered == result && Typed_checks.sequential_action e = None then Typed.rewrap (fun _ -> built) call
  else Typed_checks.of_built cx env e built
