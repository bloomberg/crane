(* WIP: dependent match returning unit in the impossible branch: the emitted C++ branch returns a unit value where the other branch returns uint64_t, so the generated function does not compile. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module DepMatchUnitVec.
Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n, A -> vec A n -> vec A (S n).
Arguments vnil {A}.
Arguments vcons {A} n _ _.
Definition head (n : nat) (v : vec nat (S n)) : nat :=
  match v in vec _ m return match m with O => unit | S _ => nat end with
  | vnil => tt
  | vcons _ x _ => x
  end.
Definition go : nat := head 0 (vcons 0 5 vnil).
End DepMatchUnitVec.
Crane Extraction "dep_match_unit_vec" DepMatchUnitVec.
