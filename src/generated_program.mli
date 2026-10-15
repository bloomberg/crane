(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What an emission generated, as a value rather than as the documents it
    was printed into.

    Each source declaration an emission generates is one entity, with the
    MiniCpp declarations generating it produced and the helpers lifted out of
    its bodies; each helper records the entity it was lifted out of.

    Transitional: generation is still driven from inside the printer's
    traversal, which records each generation as it renders it, so a file's
    program is complete only once its render is.  What it already
    establishes is identity: {!check_against_plan} holds every unit to
    "emission generates what the unit declares, and the helpers lifted out of
    it". *)

type id =
  | Source of Entity_id.t
  | Generated of Generated_entity_id.t

val compare_id : id -> id -> int
val pp_id : id -> Pp.t

module Id_set : Set.S with type elt = id

(** A helper lifted out of a body. *)
type helper = {
  helper_id : Generated_entity_id.t;
  helper_decl : Minicpp.cpp_decl;
}

(** One source declaration's generation. *)
type entity = {
  entity_id : Entity_id.t;
  decls : Minicpp.cpp_decl list;
      (** What generating it produced, before {!Cpp_pipeline.finish}. *)
  helpers : helper list;
      (** The helpers lifted out of its bodies that this generation claimed:
          a helper another entity lifted first in the same file is that
          entity's. *)
}

(** [helper d] is the helper [d] declares, if [d] is a lifted helper. *)
val helper : Minicpp.cpp_decl -> helper option

(** The globals [decls] name in their expressions and types: what has to be
    declared before them. *)
val dependencies : Minicpp.cpp_decl list -> Entity_id.Set.t

(** One phase's generated program. *)
type t

val entities : t -> entity list

(** Every helper the phase lifted, by its owner, including those no entity
    claimed. *)
val helpers : t -> helper list

(** Every entity and helper id of the program. *)
val ids : t -> Id_set.t

(** {2 Recording}

    The current phase's program is accumulated as generation happens, and
    emptied with the other per-unit state. *)

(** [record e] adds [e] to the program of the file being emitted, and
    returns it.  Nothing is generated while planning. *)
val record : entity -> entity

(** [record_helper h] notes that the file being emitted lifted [h]. *)
val record_helper : helper -> unit

(** The program the emission of file [f] of the current unit generated. *)
val emitted : Common.file -> t

(** Under [CRANE_CHECK_IR], fail unless every entity the implementation and
    header emissions generated is one the unit [declares], and every helper
    was lifted out of such an entity or out of none: emission generates what
    was planned, and the helpers its bodies lift. *)
val check_against_plan : declares:(Names.GlobRef.t -> bool) -> unit
