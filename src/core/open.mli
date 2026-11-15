(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which open annotation a {!Core.Type.Open} is.  Every annotation that shared
    one unsolved metavariable shares one [Open.t], told apart from another
    only by {!equal}; structural equality and hashing see its number alone,
    the metavariable's, which restarts with each declaration. *)

type t

(** A new open annotation, numbered [id]. *)
val fresh : int -> t

(** The annotation's number: the number of the metavariable it replaced. *)
val id : t -> int

(** Whether two values are the same annotation (the same cell), not merely
    the same number. *)
val equal : t -> t -> bool

(** A hash of {!id}, consistent with structural equality. *)
val hash : t -> int
