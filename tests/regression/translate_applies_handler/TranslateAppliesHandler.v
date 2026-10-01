From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITreeReified.
From ITree Require Import ITree.

Variant AE : Type -> Type := A0 : AE nat.
Variant BE : Type -> Type := B0 : BE nat | B1 : BE nat.

Definition relabel : AE ~> BE := fun _ e => match e with A0 => B1 end.

Module TranslateAppliesHandler.
  Definition t0 : itree AE nat := trigger A0.

  Definition relabelled : itree BE nat := translate relabel t0.
  Definition injected : itree (AE +' AE) nat := translate (fun _ e => inr1 e) t0.

  Definition which_b {X : Type} (e : BE X) : nat := match e with B0 => 0 | B1 => 1 end.
  Definition which_side {X : Type} (e : (AE +' AE) X) : nat :=
    match e with inl1 _ => 1 | inr1 _ => 2 end.

  Definition b_of (t : itree BE nat) : nat :=
    match observe t with VisF e _ => which_b e | _ => 9 end.
  Definition side_of (t : itree (AE +' AE) nat) : nat :=
    match observe t with VisF e _ => which_side e | _ => 9 end.

  Definition relabelled_event : nat := b_of relabelled.
  Definition injected_side : nat := side_of injected.
End TranslateAppliesHandler.

Crane Extraction "translate_applies_handler" TranslateAppliesHandler.
