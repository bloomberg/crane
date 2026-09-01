(** A module type whose name contains a prime.  The name is used verbatim as a
    C++ concept identifier:

    {v
      concept OrderedType' = requires { ... }
      missing terminating ' character
    v} *)

Require Crane.Extraction.

Module ConceptNameWithPrime.

Module Type Ord'. Parameter t : Set. Parameter cmp : t -> t -> bool. End Ord'.
Module NatOrd' <: Ord'. Definition t := nat. Definition cmp := Nat.eqb. End NatOrd'.
Module Use (O : Ord'). Definition same (a b : O.t) : bool := O.cmp a b. End Use.
Module U := Use NatOrd'.

Definition test : bool := U.same 1 1.

End ConceptNameWithPrime.

Crane Extraction "concept_name_with_prime" ConceptNameWithPrime.
