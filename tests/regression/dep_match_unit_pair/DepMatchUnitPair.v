(* WIP: same as dep_match_unit_vec but the payload is a pair; branch type mismatch in the emitted C++. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module DepMatchUnitPair.
Inductive tg : bool -> Type := TP : nat -> nat -> tg true | TU : tg false.
Definition get (t : tg true) : nat * nat :=
  match t in tg b return (if b then nat * nat else unit) with TP a b => (a, b) | TU => tt end.
Definition go : nat := fst (get (TP 1 2)) + snd (get (TP 1 2)).
End DepMatchUnitPair.
Crane Extraction "dep_match_unit_pair" DepMatchUnitPair.
