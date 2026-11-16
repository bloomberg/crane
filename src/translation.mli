(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Common
open Names

(** {1 Translation: Core to CppIR}

    The entry points of expression lowering, from the extracted {!Core} AST
    to the C++-oriented {!Cpp_ir} AST, for the declaration-level generators
    ({!Gen_decls} and the [Gen_*] modules), which lower each body through
    {!gen_expr} and {!gen_stmts}.

    Lowering itself is spread over modules that each own one form
    ({!Translation_expr}, {!Translation_stmts}, {!Translation_lambda},
    {!Translation_application}, {!Translation_construct},
    {!Translation_match}, {!Translation_effects},
    {!Translation_local_functions}), which recurse through
    {!Translation_knot}; this module ties that knot at load time.  What the
    generators share with lowering below it is named where it lives: the
    per-declaration context in {!Translation_state}, the position a subterm
    fills in {!Translation_slot}, type conversion in {!Translation_types},
    binder types in {!Translation_binders}, erasure judgements and coercions
    in {!Translation_erasure} and {!Translation_coerce}, call planning in
    {!Translation_calls}, and narrower questions in modules named for them
    ({!Translation_match_types}, {!Translation_lambda_params},
    {!Translation_ctor_args}, {!Translation_lifting},
    {!Translation_callable_params}, {!Translation_ownership},
    {!Translation_suspension}, {!Translation_monadic}, {!Translation_tvars},
    {!Translation_conversion}, {!Translation_naming},
    {!Translation_cpp_build}). *)

(** Generate a C++ expression from a Core expression
    ({!Translation_expr.gen_expr}).  [slot] describes the position; callers
    outside lowering leave it at {!Translation_slot.empty_slot}. *)
val gen_expr :
  Translation_state.t -> ?expected_ty:Cpp_ir.Lowered.Type.t -> ?slot:Translation_slot.slot -> env ->
    Core.Expr.t -> Cpp_ir.Lowered.Expr.t

(** Generate C++ statements from a Core expression
    ({!Translation_stmts.gen_stmts}).  The continuation [k] turns the final
    expression into a statement (a return, an assignment). *)
val gen_stmts :
  Translation_state.t -> ?slot:Translation_slot.slot ->
  env ->
  (Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t) ->
  Core.Expr.t ->
  Cpp_ir.Lowered.Stmt.t list

(** [with_method_ns_for_locals ?base f] runs [f] with the local inductives in
    scope that have recursive fields (enumerations excepted) added to
    [base] (default: the ambient {!Translation_state.method_self_ns}) as the
    method-self namespace, restoring the enclosing one on the way out however
    [f] leaves.  Containers built inside such a scope then spell those
    inductives' type parameters as their struct fields do. *)
val with_method_ns_for_locals : Translation_state.t -> ?base:Core.Ref.User.Set.t -> (unit -> 'a) -> 'a

(** [return_type_is_erased param_vars ret] -- [ret], the return type of a method
    on an inductive whose kept parameters are [param_vars], has no C++ spelling
    and must be rendered as [std::any].  Pass this to
    {!Method_registry.create}: the registry needs the judgement but is kept
    below the type translation, so it is told rather than deciding. *)
val return_type_is_erased : Translation_state.t -> Id.t list -> Core.Type.t -> bool
