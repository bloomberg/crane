From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** WIP: A `sigT` over a boolean-indexed type family whose branches are `nat` and
    `nat -> nat` extracts to a single lambda whose two branches return
    `uint64_t` and `std::any`, which clang rejects. *)

Module SigtBranchTypeMismatch.
Definition pack : sigT (fun b : bool => if b then nat else (nat -> nat)) :=
  existT _ false (fun n => n + 7).
Definition go : nat :=
  match pack with
  | existT _ true n => n
  | existT _ false f => f 1
  end.
End SigtBranchTypeMismatch.
Crane Extraction "sigt_branch_type_mismatch" SigtBranchTypeMismatch.
