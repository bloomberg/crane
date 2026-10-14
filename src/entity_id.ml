(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

module Ord = struct
  type t = GlobRef.t

  let compare = GlobRef.UserOrd.compare
end

type t = Ord.t

let of_ref r = r
let to_ref r = r
let equal = GlobRef.UserOrd.equal
let compare = Ord.compare
let pp = Printer.pr_global

module Set = Set.Make (Ord)
module Map = Map.Make (Ord)
