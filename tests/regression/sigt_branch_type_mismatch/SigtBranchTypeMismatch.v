From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** A [sigT] over a boolean-indexed type family whose branches are [nat] and
    [nat -> nat]: the payload is erased to [std::any], so the function branch
    must be called through the canonical erased-callable adapter and its
    result unboxed. *)

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
