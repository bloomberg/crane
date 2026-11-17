(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The identity of a source entity of the extracted program -- a constant,
    an inductive, a constructor -- independent of the C++ name it is printed
    under.

    Two references are one entity exactly when they are the same user
    reference ({!Names.GlobRef.UserOrd}): an [Include]d copy of a declaration
    is emitted, and called, as a declaration of its own, so the canonical
    reference, which conflates the two, does not identify it. *)

(** A source entity, compared as a user reference. *)
type t

(** The entity a reference names. *)
val of_ref : Names.GlobRef.t -> t

(** The reference the entity was made from. *)
val to_ref : t -> Names.GlobRef.t

val equal : t -> t -> bool
val compare : t -> t -> int

(** The entity as Rocq prints its reference. *)
val pp : t -> Pp.t

(** Sets and maps of entities, by user reference. *)

module Set : Set.S with type elt = t
module Map : Map.S with type key = t
