(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The identity of a declaration Crane generates that is no source
    declaration: derived from the entity it was generated for, its role
    there, and a key stable within that owner -- never from the name it is
    printed under or from the order a traversal reached it. *)

(** What the generated declaration is for its owner. *)
type role =
  | Lifted_helper of Names.Id.t
      (** A function lifted out of the owner's body, keyed by the binder it
          was bound to there. *)

type t

(** The identity of the helper [h] ({!Lifted}). *)
val lifted_helper : Lifted.t -> t

(** The source entity it was generated for; [None] for a helper lifted
    outside any declaration. *)
val owner : t -> Entity_id.t option

val role : t -> role
val equal : t -> t -> bool
val compare : t -> t -> int
val pp : t -> Pp.t
