(** Found by Ephyra round 23 (in the BDE flavour; std fails the same way).
    In a function polymorphic in [A], [let pp := (0, @inr A pt p) in
    let sb := snd pp in match sb with inl _ => 1 | inr _ => 2 end].
    Expected: compiles, [result = 2].
    Fixed: "static assertion failed ...: type not found in type list"
    (BDE: "Variant_HasUniqueType"): the match tested [sb], a [Sum<T1, pt>],
    with [std::holds_alternative<typename Sum<crane::obj, pt>::Inl>]. The
    value [(0, inr p)] does not mention [A], and extraction generalised
    [pp]'s inferred type, so [snd pp] read [A]'s position open. Once a
    let's value is extracted, what inference left open in its binder type
    is now filled from the Rocq annotation, where that names only the
    definition's own type variables. Same cause as [poly_sum_payload_obj]. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Extraction.

Module SndPairPolySumScrutinee.

Record pt := mkpt { px : nat; py : bool }.

Definition f {A : Type} (a : A) : nat :=
  let pp := (0, (@inr A pt (mkpt 0 true))) in
  let sb := snd pp in
  match sb with inl _ => 1 | inr _ => 2 end.

Definition result : nat := f true.

End SndPairPolySumScrutinee.

Crane Extraction "snd_pair_poly_sum_scrutinee" SndPairPolySumScrutinee.
