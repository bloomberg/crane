(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which open annotation a {!Type.Open} is.  Every annotation that shared
    one unsolved metavariable shares one [Open.t], told apart from another
    only by {!equal}; structural equality and hashing see its number alone,
    the metavariable's, which restarts with each declaration. *)

type t

(** A new open annotation, numbered [id]. *)
val fresh : int -> t

val id : t -> int
val equal : t -> t -> bool
val hash : t -> int
