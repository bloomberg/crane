(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Every read of a local is a read of its own.  See [fresh_reads.mli]. *)

open Miniml

let rec expr = function
  | MLrel (i, _) -> fresh_rel i
  | e -> Mlutil.ast_map expr e

let decl = function
  | Dterm (r, b, ty) -> Dterm (r, expr b, ty)
  | Dfix fds -> Dfix (List.map (fun fd -> {fd with fd_body = expr fd.fd_body}) fds)
  | d -> d

let structure = Modutil.map_struct_decls decl
