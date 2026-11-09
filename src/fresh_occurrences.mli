(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Every term of the program translation lowers is an occurrence of its
    own: every read of a local, let, match, local fixpoint and use of a
    global.

    A rewrite that copies a term copies its occurrences with it: a local
    fixpoint's outer parameters, passed again at each of its recursive calls
    once {!Mlutil.optimize_fix} has made them its own, are one read in as
    many places; a body inlined or specialized into another definition --
    [ITree.iter] into the interpreter it is specialized for, the functional
    of a well-founded recursion into the function whose knot is tied -- is
    the same uses in two definitions.  Each copy is evaluated where it
    stands, but a plan made of occurrences ({!Recursion_plan},
    {!Ownership_ir}) sees one place and must take the most cautious of its
    places for all of them.  Run after the last rewrite of Core, this gives
    each term an occurrence of its own; a term translation copies afterwards,
    having planned the original, keeps its copy's. *)

(** [term e]: [e], every occurrence in it fresh. *)
val term : Miniml.ml_ast -> Miniml.ml_ast

val structure : Miniml.ml_structure -> Miniml.ml_structure
