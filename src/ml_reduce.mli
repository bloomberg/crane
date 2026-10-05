(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A whitelisted scalar reduction, rewritten to carry an accumulator.

    One shape only: a function whose body matches on a spine argument, returns
    the unsigned zero in the base case, and in the other adds a pure
    contribution to its own result on the spine's tail, every other argument
    passed through unchanged:

    {v sum [] = 0   sum (x :: xs) = contribution x + sum xs v}

    where [+] is declared unsigned addition ({!Mapping_semantics}) at the
    width the result type is declared at.  Unsigned addition wraps, so it is
    associative and commutative at that width, and the sum can be carried
    forward instead: a local tail-recursive worker, which every declaration
    gets as a loop -- constant auxiliary space in place of a frame per
    element.  The traversal and the contribution are the source's; only the
    association of the additions moves.

    Anything else declines: another operation, an undeclared mapping, a
    contribution that is not built from declared operations, constructors and
    variables, more than one recursive call. *)

val structure : Miniml.ml_structure -> Miniml.ml_structure
