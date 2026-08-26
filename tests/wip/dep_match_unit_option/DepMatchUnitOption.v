(* WIP: same as dep_match_unit_vec but the payload is an option; branch type mismatch in the emitted C++. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module DepMatchUnitOption.
Inductive tg : bool -> Type := TO : option nat -> tg true | TU : tg false.
Definition get (t : tg true) : option nat :=
  match t in tg b return (if b then option nat else unit) with TO o => o | TU => tt end.
Definition go : nat := match get (TO (Some 4)) with Some n => n | None => 0 end.
End DepMatchUnitOption.
Crane Extraction "dep_match_unit_option" DepMatchUnitOption.
