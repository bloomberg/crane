From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** WIP: A definition whose return type is an `if` over a boolean computing `nat` in
    one branch and `nat -> nat` in the other erases to `std::any`, which is then
    applied as a function. *)

Module DependentIfTypeBranches.
Definition choose (n : nat) : if Nat.eqb n 0 then nat else (nat -> nat) :=
  match Nat.eqb n 0 as b return (if b then nat else (nat -> nat)) with
  | true => 7
  | false => fun k => k + 1
  end.
Definition go : nat := (choose 1) 41 + (choose 0).
End DependentIfTypeBranches.
Crane Extraction "dependent_if_type_branches" DependentIfTypeBranches.
