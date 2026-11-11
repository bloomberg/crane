(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Boundary checks on MiniML as it leaves extraction and its optimisations
    for translation, run under [CRANE_CHECK_IR]: every global use reaching
    translation carries a well-formed instantiation of its callee's own type
    scheme. *)

(** Checks every global use in the structure: no proof placeholder among
    its written arguments; an instantiation at the callee's own scheme, with
    one slot per variable by construction, holding no metavariable; and each
    hole held by one use, or by copies of that whole use.  A violation is an
    extraction error naming the callee and the invariant. *)
val structure : Miniml.ml_structure -> unit
