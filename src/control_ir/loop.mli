(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The identity of a ControlIR loop.  {!Term} nodes name the loop they
    enter or continue by it, and [Lower_control] keys the loops it builds by
    it. *)

(** What a loop is the loop of: a function of the program, or the member
    [m] of the local fixpoint [occurrence]. *)
type t =
  | Function of Names.GlobRef.t
  | Member of Miniml.Occurrence.t * int

(** Same function (compared as the user wrote it, {!Names.GlobRef.UserOrd}),
    or same member of the same fixpoint occurrence. *)
val equal : t -> t -> bool
