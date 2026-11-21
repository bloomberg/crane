(** Found by Ephyra (round 20). [PrimString.cat] past [max_length].

    Rocq's [cat] is total: its result is truncated to
    [PrimString.max_length] (16777211) bytes. Doubling "a" 24 times
    (2^24 = 16777216 bytes) and then prepending "xyz" both reach the bound.

    Expected: [big_clamped = true] and [clamped = true].

    Actual: both [false]. [Mapping.Std] spells [cat] as [a + b], which does
    not clamp, so the lengths are 16777216 and 16777219. ([make], fixed in
    round 19, does clamp; the fuzzer found this as [cat s (make (max_length +
    7) c)].) Also on main. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Corelib Require Import PrimString PrimInt63.
Open Scope uint63_scope.
Module StringCatMaxLength.
Fixpoint double (n : nat) (s : PrimString.string) : PrimString.string :=
  match n with O => s | S m => double m (PrimString.cat s s) end.
Definition big : PrimString.string := double 24 "a"%pstring.
Definition joined : PrimString.string := PrimString.cat "xyz"%pstring big.
Definition clamped : bool := PrimInt63.eqb (PrimString.length joined) PrimString.max_length.
Definition big_clamped : bool := PrimInt63.eqb (PrimString.length big) PrimString.max_length.
End StringCatMaxLength.
Crane Extraction "string_cat_max_length" StringCatMaxLength.
