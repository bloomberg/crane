(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type t =
  | Function of Names.GlobRef.t
  | Member of Miniml.Occurrence.t * int

let equal a b =
  match (a, b) with
  | Function g, Function g' -> Names.GlobRef.UserOrd.equal g g'
  | Member (o, m), Member (o', m') -> Miniml.Occurrence.equal o o' && Int.equal m m'
  | (Function _ | Member _), _ -> false
