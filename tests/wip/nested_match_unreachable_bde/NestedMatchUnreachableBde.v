(** Found by the BDE probe after Ephyra round 20. A match on two values of
    an enum-like inductive ([comparison]) under [Mapping.BDE].

    Expected: compiles with the BDE flavour (C++20); the program prints
    [1 0 1].

    Actual: the outer [switch] ends in [default: std::unreachable();],
    which C++23 added: "no member named 'unreachable' in namespace 'std'"
    under the BDE build's [-std=c++20]. *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Extraction.

Module NestedMatchUnreachableBde.

Definition same (c d : comparison) : bool :=
  match c, d with Eq, Eq | Lt, Lt | Gt, Gt => true | _, _ => false end.

Definition t1 : bool := same Lt Lt.
Definition t2 : bool := same Lt Gt.
Definition t3 : bool := same Gt Gt.

End NestedMatchUnreachableBde.

Crane Extraction "nested_match_unreachable_bde" NestedMatchUnreachableBde.
