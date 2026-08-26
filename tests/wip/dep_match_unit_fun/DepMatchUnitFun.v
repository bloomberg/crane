(* WIP: same as dep_match_unit_vec but the payload is a function; branch type mismatch in the emitted C++. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module DepMatchUnitFun.
Inductive tg : bool -> Type := TF : (nat -> nat) -> tg true | TU : tg false.
Definition get (t : tg true) : nat -> nat :=
  match t in tg b return (if b then nat -> nat else unit) with TF f => f | TU => tt end.
Definition go : nat := get (TF (fun x => x + 1)) 4.
End DepMatchUnitFun.
Crane Extraction "dep_match_unit_fun" DepMatchUnitFun.
