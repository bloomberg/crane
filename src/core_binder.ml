(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The Core binder a C++ local stands for.  See [core_binder.mli]. *)

type site =
  | Binding of Miniml.Occurrence.t
  | Branch of Miniml.Occurrence.t * int

type t = {
  origin : Names.GlobRef.t;
  level : int;
  site : site option;
}

let make ~origin ~level ?site () = {origin; level; site}

let equal a b = Int.equal a.level b.level && Names.GlobRef.UserOrd.equal a.origin b.origin

let same_site a b =
  match (a.site, b.site) with
  | Some (Binding o), Some (Binding o') -> Miniml.Occurrence.equal o o'
  | Some (Branch (o, i)), Some (Branch (o', i')) -> Miniml.Occurrence.equal o o' && Int.equal i i'
  | Some (Binding _), Some (Branch _) | Some (Branch _), Some (Binding _) -> false
  | None, _ | _, None -> true
