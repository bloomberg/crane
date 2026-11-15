(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** The two entry points of expression lowering that every lowering module
    recurses through: {!gen_expr} (an expression, {!Translation_expr}) and
    {!gen_stmts} (statements ending in a continuation, {!Translation_stmts}).

    Lowering is one mutually recursive function spread over several modules:
    a lambda's body is statements, a statement's right-hand side is an
    expression, an expression's match is statements again.  OCaml cannot
    recurse across compilation units, so the modules are ordered

    {v Translation_lambda < Translation_application < Translation_construct
       < Translation_match < Translation_effects < Translation_local_functions
       < Translation_stmts < Translation_expr v}

    and each calls the ones before it directly.  A call back up, to either
    entry point, goes through this module, which {!Translation} fills in once
    at load time ({!install}) with the real functions.  The two references
    are the only knot: a module that needs anything else from a later one is
    in the wrong place. *)

open Common

(** The entry points, at the types {!Translation_expr.gen_expr} and
    {!Translation_stmts.gen_stmts} have. *)
type lowering = {
  expr :
    ?expected_ty:Cpp_ir.Lowered.Type.t ->
    ?slot:Translation_support.slot ->
    env ->
    Core.Expr.t ->
    Cpp_ir.Lowered.Expr.t;
  stmts :
    ?slot:Translation_support.slot ->
    env ->
    (Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t) ->
    Core.Expr.t ->
    Cpp_ir.Lowered.Stmt.t list;
}

let installed : lowering option ref = ref None

(** Tie the knot.  Called once, by {!Translation}. *)
let install (l : lowering) = installed := Some l

let get () =
  match !installed with
  | Some l -> l
  | None -> CErrors.anomaly (Pp.str "Crane: expression lowering ran before Translation installed it.")

(** {!Translation_expr.gen_expr}. *)
let gen_expr ?expected_ty ?slot env e = (get ()).expr ?expected_ty ?slot env e

(** {!Translation_stmts.gen_stmts}. *)
let gen_stmts ?slot env k e = (get ()).stmts ?slot env k e
