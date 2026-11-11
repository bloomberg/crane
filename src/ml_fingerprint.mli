(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A digest of what a MiniML structure says, for asserting that two readers
    saw the same program.

    An analysis or plan computed from a structure can record the structure's
    fingerprint, and a later reader can compare it against the structure it
    holds: a mismatch means the structure was rewritten or mutated in between
    (an [ind_kind] demoted, an [ip_vars] renamed, a metavariable solved), and
    the recorded facts describe a different program.  {!Core_phase} uses it
    to find the elements a second normalization would still rewrite, and
    [Extract_env] to find the elements rendering changed.

    The digest is of the structure's meaning, not its representation:
    - a solved metavariable reads as its solution, so a structure does not
      change fingerprint when sharing is introduced or removed;
    - holes, unsolved metavariables and open types are numbered by first
      occurrence, so their process-wide counters do not leak in;
    - a scheme is identified by its owner and arity, not its stamp;
    - globals are spelled by their user kernel names.

    Bound module identifiers are spelled with {!Names.MBId.to_string}, which
    is stable within one process; a fingerprint is meant to be compared
    within the run that computed it. *)

(** A digest. *)
type t

(** The fingerprint of a whole structure. *)
val structure : Miniml.ml_structure -> t

(** The fingerprint of each top-level element of a structure, by label. *)
val elements : Miniml.ml_structure -> (Names.Label.t * t) list

(** The fingerprint of one declaration. *)
val decl : Miniml.ml_decl -> t

(** Whether two fingerprints are of the same program. *)
val equal : t -> t -> bool

(** The digest in hexadecimal. *)
val to_hex : t -> string
