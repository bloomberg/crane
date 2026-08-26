(* WIP: bool-indexed inductive with a dependent return type; the impossible branch returns unit and the emitted C++ has mismatched branch types. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module DepMatchUnitBoolIdx.
Inductive tagged : bool -> Type := TA : nat -> tagged true | TB : bool -> tagged false.
Definition get (t : tagged true) : nat := match t in tagged b return (if b then nat else unit) with TA n => n | TB _ => tt end.
Definition go : nat := get (TA 5).
End DepMatchUnitBoolIdx.
Crane Extraction "dep_match_unit_bool_idx" DepMatchUnitBoolIdx.
