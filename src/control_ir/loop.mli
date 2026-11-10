(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a loop is the loop of: a function of the program, or the member
    [m] of the local fixpoint [occurrence]. *)
type t =
  | Function of Names.GlobRef.t
  | Member of Miniml.Occurrence.t * int

val equal : t -> t -> bool
