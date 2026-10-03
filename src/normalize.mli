(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Normalized bodies: in a function that will be loopified, every call to
    its own recursive group that sits at a strictly evaluated, non-tail
    position is bound to a variable before the expression that uses it, in
    evaluation order.  The loop transform then meets recursive calls only as
    [auto r = f(...);] statements, a tail [return f(...)], or the last
    recursive argument of a constructor that builds a cell -- what tail modulo
    cons rewrites.

    MiniML is pure and strict, so binding an argument before its application
    preserves meaning; nothing is taken out of a branch, a lambda body or a
    let body, which may not run. *)

(** [structure s] normalizes every loopified fixpoint group in [s]. *)
val structure : Miniml.ml_structure -> Miniml.ml_structure
