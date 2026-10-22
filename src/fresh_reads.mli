(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Every read of a local in the program translation lowers is a read of
    its own.

    A rewrite that copies a term copies its reads' occurrences with it: a
    local fixpoint's outer parameters, passed again at each of its recursive
    calls once {!Mlutil.optimize_fix} has made them its own, are one read in
    as many places.  Each copy is evaluated where it stands, but a plan made
    of the reads ({!Ownership_plan}) sees one read and must take the most
    cautious of its places for all of them.  Run after the last rewrite of
    Core, this gives each read an occurrence of its own; a term translation
    copies afterwards, having planned the original, keeps its copy's. *)

val structure : Miniml.ml_structure -> Miniml.ml_structure
