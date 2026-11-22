(** Found by Ephyra round 23 (in the BDE flavour; std fails the same way).
    In a function polymorphic in [A], [let pp := (0, @inr A pt p) in
    let sb := snd pp in match sb with inl _ => 1 | inr _ => 2 end]. [sb] is
    a [Sum<T1, pt>], but the match tests it with
    [std::holds_alternative<typename Sum<crane::obj, pt>::Inl>(sb.v_mut())]:
    the scrutinee's type, read through the [snd] projection, has [A]
    erased to [crane::obj], and [Sum<crane::obj, pt>::Inl] is not an
    alternative of [Sum<T1, pt>]'s variant. Matching on
    [@inr A pt p] directly compiles.
    Expected: compiles, [result = 2].
    Actual: "static assertion failed ...: type not found in type list"
    (BDE: "Variant_HasUniqueType"). Also on main. *)
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
