From Crane Require Import Mapping.NatInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import PArith.

(** [positive] has no zero: Rocq's [Pos.sub x y] is 1 when [x <= y], and
    [Pos.pred 1] is 1.  Mapping.NInt printed both as plain unsigned
    subtraction, so [Pos.sub 2 5] wrapped around and [Pos.pred 1] was 0. *)
Module PosSubSaturates.

Definition s (x y : positive) : positive := Pos.sub x y.
Definition p (x : positive) : positive := Pos.pred x.
Definition t : positive := Pos.sub 2 5.

End PosSubSaturates.

Crane Extraction "pos_sub_saturates" PosSubSaturates.
