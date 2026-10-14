(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The bridge from a unit's {!Program_facts} and {!Target_plan} to the tables
    the readers not yet converted consult: filled once, from the values,
    before anything is rendered. *)

(** [install struc facts plan] fills the legacy tables, and writes each
    decided inductive kind into the structure's declarations of that block,
    which most readers still take the kind from. *)
val install : Miniml.ml_structure -> Program_facts.t -> Target_plan.t -> unit

(** Under [CRANE_CHECK_IR], fail unless every table {!install} filled still
    answers what the values say.  A census sees an entry added; this sees one
    overwritten.  The used customs are the exception that may grow: emitting a
    custom's replacement marks it used, and the header's includes follow what
    was emitted. *)
val check_installed : Program_facts.t -> Target_plan.t -> unit
