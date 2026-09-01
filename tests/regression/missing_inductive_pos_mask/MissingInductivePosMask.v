(** [Pos.mask] is referenced by the extracted signature of [Pos.sub_mask] but
    the inductive itself is never emitted:

    {v
      unknown type name 'mask'
    v} *)

From Crane.Mapping Require Import Std.
Require Import BinPos.

Module MissingInductivePosMask.

Definition f (p q : positive) : Pos.mask := Pos.sub_mask p q.

End MissingInductivePosMask.

Crane Extraction "missing_inductive_pos_mask" MissingInductivePosMask.
