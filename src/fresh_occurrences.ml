(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Every term is an occurrence of its own.  See [fresh_occurrences.mli]. *)

open Miniml

let rec term e =
  match Mlutil.ast_map term e with
  | MLrel (i, _) -> fresh_rel i
  | MLletin (x, ty, a, b, _) -> MLletin (x, ty, a, b, Occurrence.fresh ())
  | MLfix (i, ids, bodies, cofix, _) -> MLfix (i, ids, bodies, cofix, Occurrence.fresh ())
  | MLglob use -> MLglob (Global_use.refresh use)
  | e -> e

let decl = function
  | Dterm (r, b, ty) -> Dterm (r, term b, ty)
  | Dfix fds -> Dfix (List.map (fun fd -> {fd with fd_body = term fd.fd_body}) fds)
  | d -> d

let structure = Modutil.map_struct_decls decl
