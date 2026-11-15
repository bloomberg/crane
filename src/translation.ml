(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Core to CppIR translation: the entry points the declaration generators
    call.  Expression lowering is spread over modules that each own one form
    ({!Translation_expr}, {!Translation_stmts}, {!Translation_lambda},
    {!Translation_application}, {!Translation_construct},
    {!Translation_match}, {!Translation_effects},
    {!Translation_local_functions}); this driver ties their recursion
    ({!Translation_knot}) and the forward references of the layers below
    them, once, at load time. *)

open Names

let gen_expr = Translation_expr.gen_expr
let gen_stmts = Translation_stmts.gen_stmts

let () = Translation_knot.install {expr = Translation_expr.gen_expr; stmts = Translation_stmts.gen_stmts}
let () = Translation_types.type_term_arg := fun env a -> gen_expr env a
let () = Translation_state.plan_representation := Representation_plan.region
let () = Translation_state.plan_positions := Position_plan.region

(** [with_method_ns_for_locals ?base f] runs [f] with the module's local
    inductives added to {!Translation_state.method_self_ns}, and puts the
    enclosing namespace back on the way out however [f] leaves.

    Functions inside wrapper modules (e.g. Cotree.tree_of_cotree) construct
    containers whose type parameters must use shared_ptr for recursive
    value-type inductives, matching struct field types.

    @param base  The namespace to extend, when the caller has one of its own in
      hand.  Defaults to the ambient {!Translation_state.method_self_ns}. *)
let with_method_ns_for_locals ?base (f : unit -> 'a) : 'a =
  let full_ns =
    List.fold_left
      (fun acc g ->
        if Table.has_recursive_fields g && not (Table.is_enum_inductive g)
        then Ref.User.Set.add g acc
        else acc)
      (Option.default (!Translation_state.tctx).input.method_self_ns base)
      (Translation_state.local_inductives_in_scope ())
  in
  Translation_state.with_method_self_ns full_ns f

(** [return_type_is_erased param_vars ret] -- [ret], the return type of a method
    on an inductive whose kept parameters are [param_vars], has no C++ spelling
    and must be rendered as [std::any].

    This is the judgement {!Method_registry.create} asks for.  It lives here
    because it is a question about C++ types, and the registry is deliberately
    kept below the type translation. *)
let return_type_is_erased (param_vars : Id.t list) (ret : Core.Type.t) : bool =
  Type_util.type_is_erased (Translation_types.cpp_ir_of_core_type (Common.empty_env ()) param_vars ret)
