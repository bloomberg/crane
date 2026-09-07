From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Utils.HAList.
From Stdlib Require Import List Classes.EquivDec.
Import ListNotations.

(** [halist K V] is indexed by a value family [V : K -> Type].  Crane gives
    [halist_add] the signature [halist<T1,T2> halist_add(EqDec<T1>, T1 k, T2 v,
    ...)] -- the same template parameter [T2] stands for the family and for the
    value.  [T2] is deduced as [vty] from the map argument, so passing a
    [uint64_t] for [v] leaves no viable overload. *)

Module HalistDependentValue.

  Inductive key := KNat | KList.

  Definition vty (k : key) : Type :=
    match k with
    | KNat => nat
    | KList => list nat
    end.

  #[export] Instance keyEq : EqDec key eq.
  Proof.
    intros x y; destruct x, y;
      try (left; reflexivity); right; discriminate.
  Defined.

  Definition m0 : halist key vty := [].
  Definition m1 := halist_add key vty KNat 7 m0.
  Definition m2 := halist_add key vty KList [1;2;3] m1.

  Definition run : nat :=
    match halist_lookup key vty KNat m2 with Some n => n | None => 0 end
    + match halist_lookup key vty KList m2 with Some l => List.length l | None => 0 end.

End HalistDependentValue.

Crane Extraction "halist_dependent_value" HalistDependentValue.
