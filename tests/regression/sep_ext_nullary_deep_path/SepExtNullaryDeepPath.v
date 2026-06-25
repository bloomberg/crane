(** Regression: accessing a nullary field through a 3-level nested module
    path inside a functor must emit () in C++.
    Pattern: R.M.L.val where R is a functor parameter whose module type
    declares nested sub-modules M and L, with val being a nullary field
    at the leaf.
    This mirrors the TabT.R.Ty.SigmaEnum and D.Defs.NtSet.empty patterns
    in the parse-a-lot benchmark. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.

Module Type Leaf.
  Parameter val : nat.
  Parameter extra : nat.
End Leaf.

Module Type Mid.
  Declare Module L : Leaf.
End Mid.

Module Type Root.
  Declare Module M : Mid.
End Root.

Module Worker (R : Root).

  Definition deep_val : nat := R.M.L.val.

  Definition deep_extra : nat := R.M.L.extra.

  Definition deep_sum : nat := Nat.add R.M.L.val R.M.L.extra.

End Worker.

Crane Separate Extraction Worker.
