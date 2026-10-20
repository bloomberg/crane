(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type t = {
  origin : Names.GlobRef.t;
  level : int;
  site : Miniml.Occurrence.t option;
}

let make ~origin ~level ?site () = {origin; level; site}

let equal a b = Int.equal a.level b.level && Names.GlobRef.UserOrd.equal a.origin b.origin

let same_site a b =
  match (a.site, b.site) with
  | Some s, Some s' -> Miniml.Occurrence.equal s s'
  | None, _ | _, None -> true
