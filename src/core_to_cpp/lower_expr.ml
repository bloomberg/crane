(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Core to CppIR translation: the entry points the declaration generators
    call.  Expression lowering is spread over modules that each own one form
    ({!Expr}, {!Stmts}, {!Lambda},
    {!Application}, {!Construction},
    {!Match}, {!Effects},
    {!Local_functions}); this driver ties their recursion
    ({!Knot}) and the forward references of the layers below
    them, once, at load time. *)

open Names

let gen_expr_typed = Expr.gen_expr_typed
let gen_stmts = Stmts.gen_stmts

let () = Knot.install {expr_typed = Expr.gen_expr_typed; stmts = Stmts.gen_stmts}
let () = Types.type_term_arg := fun cx env a -> (gen_expr_typed cx (Slot.at ~ret:None ()) env a).expr
let () = Lowering_state.plan_representation := Representation_plan.region
let () = Lowering_state.plan_positions := Position_plan.region

(** [with_method_ns_for_locals ?base f] runs [f] with the module's local
    inductives added to {!Lowering_state.method_self_ns}, and puts the
    enclosing namespace back on the way out however [f] leaves.

    Functions inside wrapper modules (e.g. Cotree.tree_of_cotree) construct
    containers whose type parameters must use shared_ptr for recursive
    value-type inductives, matching struct field types.

    @param base  The namespace to extend, when the caller has one of its own in
      hand.  Defaults to the ambient {!Lowering_state.method_self_ns}. *)
let with_method_ns_for_locals cx ?base (f : unit -> 'a) : 'a =
  let full_ns =
    List.fold_left
      (fun acc g ->
        if Base.Table.has_recursive_fields g && not (Base.Table.is_enum_inductive g)
        then Core.Ref.User.Set.add g acc
        else acc)
      (Option.default cx.Lowering_state.ctx.input.method_self_ns base)
      (Lowering_state.local_inductives_in_scope cx)
  in
  Lowering_state.with_method_self_ns cx full_ns f

(** [return_type_is_erased param_vars ret] -- [ret], the return type of a method
    on an inductive whose kept parameters are [param_vars], has no C++ spelling
    and must be rendered as [std::any].

    This is the judgement {!Core_plan.Method_registry.create} asks for.  It lives here
    because it is a question about C++ types, and the registry is deliberately
    kept below the type translation. *)
let return_type_is_erased cx (param_vars : Id.t list) (ret : Core.Type.t) : bool =
  Base.Type_util.type_is_erased (Types.cpp_ir_of_core_type cx (Base.Common.empty_env ()) param_vars ret)
