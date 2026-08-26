(* WIP: same as dep_match_unit_vec but the payload is a list; branch type mismatch in the emitted C++. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Module DepMatchUnitList.
Inductive tg : bool -> Type := TL : list nat -> tg true | TU : tg false.
Definition get (t : tg true) : list nat :=
  match t in tg b return (if b then list nat else unit) with TL l => l | TU => tt end.
Definition go : nat := length (get (TL (cons 1 nil))).
End DepMatchUnitList.
Crane Extraction "dep_match_unit_list" DepMatchUnitList.
