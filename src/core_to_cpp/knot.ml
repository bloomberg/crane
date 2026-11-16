(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** The two entry points of expression lowering that every lowering module
    recurses through: {!gen_expr} (an expression, {!Expr}) and
    {!gen_stmts} (statements ending in a continuation, {!Stmts}).

    Lowering is one mutually recursive function spread over several modules:
    a lambda's body is statements, a statement's right-hand side is an
    expression, an expression's match is statements again.  OCaml cannot
    recurse across compilation units, so the modules are ordered

    {v Translation_lambda < Translation_application < Translation_construct
       < Translation_match < Translation_effects < Translation_local_functions
       < Translation_stmts < Translation_expr v}

    and each calls the ones before it directly.  A call back up, to either
    entry point, goes through this module, which {!Lower_expr} fills in once
    at load time ({!install}) with the real functions.  The two references
    are the only knot: a module that needs anything else from a later one is
    in the wrong place. *)

open Base.Common

(** The entry points, at the types {!Expr.gen_expr} and
    {!Stmts.gen_stmts} have. *)
type lowering = {
  expr :
    Lowering_state.t ->
    ?expected_ty:Cpp_ir.Lowered.Type.t ->
    ?slot:Slot.slot ->
    env ->
    Core.Expr.t ->
    Cpp_ir.Lowered.Expr.t;
  stmts :
    Lowering_state.t ->
    ?slot:Slot.slot ->
    env ->
    (Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t) ->
    Core.Expr.t ->
    Cpp_ir.Lowered.Stmt.t list;
}

(** The installed entry points; [None] until {!Lower_expr} loads. *)
let installed : lowering option ref = ref None

(** Tie the knot.  Called once, by {!Lower_expr}. *)
let install (l : lowering) = installed := Some l

(** The installed entry points.  An anomaly if lowering runs before
    {!install}. *)
let get () =
  match !installed with
  | Some l -> l
  | None -> CErrors.anomaly (Pp.str "Crane: expression lowering ran before Translation installed it.")

(** {!Expr.gen_expr}. *)
let gen_expr cx ?expected_ty ?slot env e = (get ()).expr cx ?expected_ty ?slot env e

(** {!Stmts.gen_stmts}. *)
let gen_stmts cx ?slot env k e = (get ()).stmts cx ?slot env k e
