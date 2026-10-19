(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type t = {
  origin : Names.GlobRef.t;
  level : int;
}

let make ~origin ~level = {origin; level}

let equal a b = Int.equal a.level b.level && Names.GlobRef.UserOrd.equal a.origin b.origin
