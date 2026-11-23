(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Compiled interfaces (design 20): what a C++ unit's header was written
    against, so that a unit including it agrees.

    When an extraction finishes, {!record} persists in the [.vo], beside
    the unit's claim on its Rocq libraries
    ({!Table.claim_extracted_unit}), one entry per typed-mapped head the
    extraction compiled a plan for -- a type ({!Mapping_plan}) or an
    operation ({!Mapping_operation}): the instance selected, and a digest
    of the physical ABI the plan compiles to (canonical type, components,
    copy, access, views and their escape, constructor plans, value and
    lifetime model, release plan, headers; for an operation its template,
    argument uses and forms, result, facts and purity).

    A later extraction in another file that includes the unit's header
    {!check}s each entry against its own resolution of the head, before it
    lowers anything: a different instance, a different ABI, or no typed
    mapping at all is a user error naming both. *)

(** Record, for the unit [target], every head this extraction compiled a
    typed plan for. *)
val record : string -> unit

(** Check the entries recorded for the units [targets] against this
    extraction's resolution of their heads. *)
val check : string list -> unit
