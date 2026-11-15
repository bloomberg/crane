(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which occurrence of a node a Core term holds: made fresh where the node
    is built, and kept by every rewrite of its types, so that a pass can find
    the node it planned in a term the annotation rewrites rebuilt.
    Occurrences are told apart only by {!equal}; to structural equality and
    hashing every occurrence is the same, so two terms that differ only in
    where they were built still compare equal. *)

type t

(** A new occurrence, for a term built rather than copied: a copy keeps
    the occurrence of what it copies. *)
val fresh : unit -> t

val equal : t -> t -> bool

(** [shared iter]: the occurrences [iter] visits more than once, each
    listed once, in the order of its second visit.  [iter] is run twice,
    and must visit the same occurrences each time. *)
val shared : ((t -> unit) -> unit) -> t list
