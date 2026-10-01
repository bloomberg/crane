From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import NArith.

(* The collision with the type [N] forces this file's own declarations into a
   struct named after the file (the d51249392 path). *)
Module N.
  Definition two : N := 2%N.
End N.

Variant dval : Set := DV_nat (n : nat).
Definition mk (n : nat) : dval := DV_nat n.
