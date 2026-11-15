(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Every term is an occurrence of its own.  See [fresh_occurrences.mli]. *)

open Miniml

(* A group recursing at a ground instance stays one under its new
   occurrence ({!Table.add_erased_fix_group}). *)
let fix_occurrence occ =
  let occ' = Occurrence.fresh () in
  if Table.is_erased_fix_group occ then Table.add_erased_fix_group occ';
  occ'

let rec term e =
  match Mlutil.ast_map term e with
  | MLrel (i, _) -> fresh_rel i
  | MLletin (x, ty, a, b, _) -> MLletin (x, ty, a, b, Occurrence.fresh ())
  | MLcase (ty, scrut, branches, _) -> MLcase (ty, scrut, branches, Occurrence.fresh ())
  | MLcons (ty, r, args, _) -> MLcons (ty, r, args, Occurrence.fresh ())
  | MLmagic (m, a, _) -> MLmagic (m, a, Occurrence.fresh ())
  | MLfixpoint (i, ids, bodies, occ) -> MLfixpoint (i, ids, bodies, fix_occurrence occ)
  | MLcofixpoint (i, ids, bodies, occ) -> MLcofixpoint (i, ids, bodies, fix_occurrence occ)
  | MLglob use -> MLglob (Global_use.refresh use)
  | e -> e

let decl = function
  | Dterm (r, b, ty) -> Dterm (r, term b, ty)
  | Dfix fds -> Dfix (List.map (fun fd -> {fd with fd_body = term fd.fd_body}) fds)
  | d -> d

let structure = Modutil.map_struct_decls decl
