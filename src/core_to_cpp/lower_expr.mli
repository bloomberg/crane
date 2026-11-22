(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Base.Common
open Names

(** {1 Translation: Core to CppIR}

    The entry points of expression lowering, from the extracted {!Core} AST
    to the C++-oriented {!Cpp_ir} AST, for the declaration-level generators
    ({!Lower_decl} and the [Gen_*] modules), which lower each body through
    {!gen_expr} and {!gen_stmts}.

    Lowering itself is spread over modules that each own one form
    ({!Expr}, {!Stmts}, {!Lambda},
    {!Application}, {!Construction},
    {!Match}, {!Effects},
    {!Local_functions}), which recurse through
    {!Knot}; this module ties that knot at load time.  What the
    generators share with lowering below it is named where it lives: the
    per-declaration context in {!Lowering_state}, the position a subterm
    fills in {!Slot}, type conversion in {!Types},
    binder types in {!Binders}, erasure judgements and coercions
    in {!Erasure} and {!Coerce}, call planning in
    {!Calls}, and narrower questions in modules named for them
    ({!Match_types}, {!Lambda_params},
    {!Ctor_args}, {!Lifting},
    {!Callable_params}, {!Ownership},
    {!Suspension}, {!Monadic}, {!Tvars},
    {!Convert}, {!Naming},
    {!Cpp_build}). *)

(** Generate a C++ expression from a Core expression
    ({!Expr.gen_expr}).  [slot] describes the position; callers
    outside lowering leave it at {!Slot.empty_slot}. *)
val gen_expr :
  Lowering_state.t -> ?expected_ty:Cpp_ir.Lowered.Type.t -> ?slot:Slot.slot -> env ->
    Core.Expr.t -> Cpp_ir.Lowered.Expr.t

(** Generate C++ statements from a Core expression
    ({!Stmts.gen_stmts}).  The final value goes to the {!Destination}
    (a return, an assignment). *)
val gen_stmts :
  Lowering_state.t -> ?slot:Slot.slot ->
  env ->
  Destination.t ->
  Core.Expr.t ->
  Cpp_ir.Lowered.Stmt.t list

(** [with_method_ns_for_locals ?base f] runs [f] with the local inductives in
    scope that have recursive fields (enumerations excepted) added to
    [base] (default: the ambient {!Lowering_state.method_self_ns}) as the
    method-self namespace, restoring the enclosing one on the way out however
    [f] leaves.  Containers built inside such a scope then spell those
    inductives' type parameters as their struct fields do. *)
val with_method_ns_for_locals : Lowering_state.t -> ?base:Core.Ref.User.Set.t -> (unit -> 'a) -> 'a

(** [return_type_is_erased param_vars ret] -- [ret], the return type of a method
    on an inductive whose kept parameters are [param_vars], has no C++ spelling
    and must be rendered as [std::any].  Pass this to
    {!Core_plan.Method_registry.create}: the registry needs the judgement but is kept
    below the type translation, so it is told rather than deciding. *)
val return_type_is_erased : Lowering_state.t -> Id.t list -> Core.Type.t -> bool
