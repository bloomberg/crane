(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

let apply = Mlutil.canonical_app

let spine = Mlutil.canonical

let canonical_head = function
  | MLapp (MLglob _, _) | MLmagic _ -> false
  | MLcase (_, _, [|_|], _) -> false
  | _ -> true

let structure =
  Modutil.map_struct_decls (function
    | Dterm (r, b, ty) -> Dterm (r, spine b, ty)
    | Dfix fds -> Dfix (List.map (fun fd -> {fd with fd_body = spine fd.fd_body}) fds)
    | d -> d )
