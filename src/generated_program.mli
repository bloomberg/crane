(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a unit generated, as a value rather than as the documents it was
    printed into.

    Each source declaration generated is one entity, with the MiniCpp
    declarations generating it produced and the helpers lifted out of its
    bodies; each helper records the entity it was lifted out of.

    The unit's program is recorded as the walk ahead of the files generates
    it ({!record_ahead}, {!record_lifted_ahead}): the bodies a generation
    translates lift its helpers, and the walk records them; nothing records
    a helper as it is lifted.  Each file's render records the entities it
    takes from there ({!record}).  {!check_against_ahead} holds the two to
    the same entities, and {!check_against_plan} holds every unit to
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

(** The globals [decls] name ({!Minicpp.iter_globrefs}): what has to be
    declared before them. *)
val dependencies : Minicpp.cpp_decl list -> Entity_id.Set.t

(** One phase's generated program. *)
type t

val entities : t -> entity list

(** Every entity and helper id of the program. *)
val ids : t -> Id_set.t

(** {2 Recording}

    The current phase's program is accumulated as generation happens, and
    emptied with the other per-unit state. *)

(** [record e] adds [e] to what the files have taken, and returns it.
    Nothing is generated while planning. *)
val record : entity -> entity

(** Under [CRANE_CHECK_IR], fail unless every entity generated ahead of the
    files or taken by them is one the unit [declares], and every helper was
    lifted out of such an entity or out of none: emission generates what was
    planned, and the helpers its bodies lift. *)
val check_against_plan : declares:(Names.GlobRef.t -> bool) -> unit

(** [record_ahead e] adds [e], and the helpers lifted out of it, to the
    unit's program as the walk ahead of the files generates it. *)
val record_ahead : entity -> unit

(** [record_lifted_ahead ds] adds the helpers among [ds], lifted by some
    generation of the walk ahead of the files, to the unit's program.  Under
    [CRANE_CHECK_IR] a helper is lifted by one generation: a second
    declaration of one already recorded is a violation, the same declaration
    handed on to another generation is not. *)
val record_lifted_ahead : Minicpp.cpp_decl list -> unit

(** Under [CRANE_CHECK_IR], fail unless the entities the two files took,
    with the helpers they claimed, are exactly those generated ahead of
    them: the walk ahead generates what the renders write, and nothing
    else. *)
val check_against_ahead : unit -> unit
