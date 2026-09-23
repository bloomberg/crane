From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

(** A class that is also used in value position comes out as a struct, not a
    concept.  A field of that type is then an ordinary value field, so
    promoting it to an associated type leaves the concept asking for one name
    both as a type and as a function -- which no instance can satisfy. *)
Class VLike (I : Type) := {
  vzero : I;
  vadd : I -> I -> I;
}.

(** These two put [VLike] in value position, which demotes it to a struct. *)
Definition mk_vlike (I : Type) (z : I) (f : I -> I -> I) : VLike I :=
  {| vzero := z; vadd := f |}.

Definition dicts : list (VLike nat) := cons (mk_vlike nat 0 Nat.add) nil.

Class Ptr := {
  iptr : Type;
  VLike_iptr : VLike iptr;
  one_iptr : iptr;
}.

Module ValuePositionClassPromoted.
  Section S.
    Context `{Ptr}.

    Definition twice : iptr := @vadd iptr VLike_iptr one_iptr one_iptr.
  End S.

  (** Reaches [dicts], so the value-position use is not pruned. *)
  Definition ndicts : nat := match dicts with nil => 0 | cons d _ => @vzero nat d end.

End ValuePositionClassPromoted.

Crane Extraction "value_position_class_promoted" ValuePositionClassPromoted.
