(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Small closed definitions evaluated at extraction time, within a fixed
    budget.

    A definition whose value is an unsigned integer ({!Mapping_semantics}) or
    a constant of an enumeration -- [test_map := fold_left add (map (mul 2)
    [1;...;5]) 0] -- is computed by following the program as written: its
    constructors, its functions' own bodies, its declared operations.  Every
    step and every value built is charged against the budget; running out,
    or reaching an operation with no declared meaning -- an undeclared
    mapping, a primitive, an effect -- leaves the definition exactly as it
    was.  Nothing is computed by a formula the program does not spell. *)

val structure : Miniml.ml_structure -> Miniml.ml_structure
