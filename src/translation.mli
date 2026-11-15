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
    per-declaration context in {!Translation_state}, type conversion and
    binder types in {!Translation_types}, call planning in
    {!Translation_calls}, and the rest in {!Translation_support}. *)

(** Generate a C++ expression from a Core expression
    ({!Translation_expr.gen_expr}).  [slot] describes the position; callers
    outside lowering leave it at {!Translation_support.empty_slot}. *)
val gen_expr :
  ?expected_ty:Cpp_ir.Lowered.Type.t -> ?slot:Translation_support.slot -> env -> Core.Expr.t -> Cpp_ir.Lowered.Expr.t

(** Generate C++ statements from a Core expression
    ({!Translation_stmts.gen_stmts}).  The continuation [k] turns the final
    expression into a statement (a return, an assignment). *)
val gen_stmts :
  ?slot:Translation_support.slot ->
  env ->
  (Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t) ->
  Core.Expr.t ->
  Cpp_ir.Lowered.Stmt.t list

(** [with_method_ns_for_locals () f] runs [f] with the module's local
    inductives added to [method_self_ns], restoring the enclosing namespace on
    the way out however [f] leaves. *)
val with_method_ns_for_locals : ?base:Ref.User.Set.t -> (unit -> 'a) -> 'a

(** [return_type_is_erased param_vars ret] -- [ret], the return type of a method
    on an inductive whose kept parameters are [param_vars], has no C++ spelling
    and must be rendered as [std::any].  Pass this to
    {!Method_registry.create}: the registry needs the judgement but is kept
    below the type translation, so it is told rather than deciding. *)
val return_type_is_erased : Id.t list -> Core.Type.t -> bool
