(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** MiniCpp read through declared meanings.  See [cpp_declared.mli]. *)

open Minicpp

let applied e =
  match e with
  | CPPfun_call (_, CPPglob (r, _, _), args) ->
    Option.map (fun m -> (m, call_args args)) (Mapping_semantics.find r)
  | CPPglob (r, _, _) -> Option.map (fun m -> (m, [])) (Mapping_semantics.find r)
  | _ -> None
