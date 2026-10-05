(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Small local simplifications.  See [cpp_simplify.mli]. *)

open Names
open Minicpp

(* A [bool]: what a comparison or a connective yields. *)
let is_bool = function
  | CPPbinop ((Beq | Bneq | Band | Bor), _, _) | CPPunop (Unot, _) | CPPbool _ -> true
  | _ -> false

(* Drop each binding of a pure value nothing after it reads or assigns. *)
let rec drop_unused = function
  | [] -> []
  | Sasgn (x, Declare _, e) :: rest
    when pure_expr e
         && (not (List.exists (Id.equal x) (free_vars_body rest)))
         && not (Id.Set.mem x (assigned_vars rest)) ->
    drop_unused rest
  | s :: rest -> s :: drop_unused rest

let rec stmts ss = drop_unused (List.map stmt ss)

and stmt s =
  match s with
  | Sif (c, t, e) -> (
    match expr c with
    | CPPbool b -> Sblock (stmts (if b then t else e))
    | c -> (
      match (stmts t, stmts e) with
      | [Sreturn (Some (CPPbool true))], [Sreturn (Some (CPPbool false))] when is_bool c ->
        Sreturn (Some c)
      | t, e -> Sif (c, t, e) ) )
  | _ -> map_stmt ~fl:stmts expr stmt Fun.id s

and expr e =
  match e with
  | CPPcond (CPPbool b, x, y) -> expr (if b then x else y)
  | _ -> map_expr ~fl:stmts expr stmt Fun.id e

let transform_decl d = map_decl ~fl:stmts expr stmt Fun.id d
