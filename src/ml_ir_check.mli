(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Boundary checks on MiniML as it leaves extraction and its optimisations
    for translation, run under [CRANE_CHECK_IR]
    (docs/Type-Argument-Numbering-Refactor-Plan.md, section 8.1). *)

(** Checks every global use in the structure.  A violation is an extraction
    error naming the callee and the invariant. *)
val structure : Miniml.ml_structure -> unit
