(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: opposite-property transfer via the theorem-doubling path. *)

From Stdlib Require Import Lia Nat.

Module OppositePropertyTransferTraceCase.

Record PreStableCategory := {
  ps_tag : nat;
  ps_shift : nat;
  ps_Susp : nat -> nat;
  ps_Loop : nat -> nat;
  ps_eta : nat -> nat;
  ps_epsilon : nat -> nat
}.

Definition opposite_prestable_category (PS : PreStableCategory)
  : PreStableCategory :=
  {| ps_tag := ps_tag PS;
     ps_shift := ps_shift PS;
     ps_Susp := ps_Loop PS;
     ps_Loop := ps_Susp PS;
     ps_eta := ps_epsilon PS;
     ps_epsilon := ps_eta PS |}.

Record LeftStableWitness (PS : PreStableCategory) := {
  lsw_seed : nat;
  lsw_value : nat;
  lsw_ok : lsw_value = ps_eta PS lsw_seed
}.

Record RightStableWitness (PS : PreStableCategory) := {
  rsw_seed : nat;
  rsw_value : nat;
  rsw_ok : rsw_value = ps_epsilon PS rsw_seed
}.

Record Triangle1Witness (PS : PreStableCategory) := {
  t1_seed : nat;
  t1_value : nat;
  t1_ok : t1_value = ps_Susp PS (ps_eta PS t1_seed)
}.

Record Triangle2Witness (PS : PreStableCategory) := {
  t2_seed : nat;
  t2_value : nat;
  t2_ok : t2_value = ps_Loop PS (ps_epsilon PS t2_seed)
}.

Definition is_left_semi_stable (PS : PreStableCategory) : Type :=
  LeftStableWitness PS.

Definition is_right_semi_stable (PS : PreStableCategory) : Type :=
  RightStableWitness PS.

Definition satisfies_triangle_1 (PS : PreStableCategory) : Type :=
  Triangle1Witness PS.

Definition satisfies_triangle_2 (PS : PreStableCategory) : Type :=
  Triangle2Witness PS.

Definition EquivT (A B : Type) : Type := (A -> B) * (B -> A).

Record LeftProperty (PS : PreStableCategory) := {
  lp_seed : nat;
  lp_value : nat;
  lp_tag : nat;
  lp_ok : lp_value = ps_eta PS lp_seed + ps_shift PS + lp_tag
}.

Record RightProperty (PS : PreStableCategory) := {
  rp_seed : nat;
  rp_value : nat;
  rp_tag : nat;
  rp_ok : rp_value = ps_epsilon PS rp_seed + ps_shift PS + rp_tag
}.

Arguments lp_seed {PS} _.
Arguments lp_value {PS} _.
Arguments lp_tag {PS} _.
Arguments rp_seed {PS} _.
Arguments rp_value {PS} _.
Arguments rp_tag {PS} _.

Lemma right_stable_gives_opposite_left (PS : PreStableCategory)
  : is_right_semi_stable PS ->
    is_left_semi_stable (opposite_prestable_category PS).
Proof.
  intro H.
  destruct H as [seed value Hok].
  refine {| lsw_seed := seed; lsw_value := value |}.
  exact Hok.
Defined.

Lemma triangle_identity_duality (PS : PreStableCategory)
  : EquivT (satisfies_triangle_1 PS)
      (satisfies_triangle_2 (opposite_prestable_category PS)).
Proof.
  split.
  - intro H.
    destruct H as [seed value Hok].
    refine {| t2_seed := seed; t2_value := value |}.
    exact Hok.
  - intro H.
    destruct H as [seed value Hok].
    refine {| t1_seed := seed; t1_value := value |}.
    exact Hok.
Defined.

Definition sample_left_property (PS : PreStableCategory)
    (H_left : is_left_semi_stable PS)
    (_H_tri1 : satisfies_triangle_1 PS)
  : LeftProperty PS.
Proof.
  destruct H_left as [seed value Hvalue].
  refine
    {| lp_seed := seed;
       lp_value := value + ps_shift PS + ps_tag PS;
       lp_tag := ps_tag PS |}.
  rewrite Hvalue.
  lia.
Defined.

Lemma dual_property_equiv (PS : PreStableCategory)
  : EquivT (LeftProperty PS) (RightProperty (opposite_prestable_category PS)).
Proof.
  split.
  - intro H.
    destruct H as [seed value tag Hok].
    refine {| rp_seed := seed; rp_value := value; rp_tag := tag |}.
    exact Hok.
  - intro H.
    destruct H as [seed value tag Hok].
    refine {| lp_seed := seed; lp_value := value; lp_tag := tag |}.
    exact Hok.
Defined.

Lemma double_opposite_involutive (PS : PreStableCategory)
  : opposite_prestable_category (opposite_prestable_category PS) = PS.
Proof.
  destruct PS as [tag shift susp loop eta epsilon].
  reflexivity.
Qed.

Theorem theorem_doubling_principle_correct
  (P : PreStableCategory -> Type)
  (Q : PreStableCategory -> Type)
  (H_dual : forall PS, EquivT (P PS) (Q (opposite_prestable_category PS)))
  (H_theorem : forall PS, is_left_semi_stable PS -> satisfies_triangle_1 PS -> P PS)
  (H_invol : forall PS, opposite_prestable_category (opposite_prestable_category PS) = PS)
  : forall PS,
    is_left_semi_stable (opposite_prestable_category PS) ->
    satisfies_triangle_1 (opposite_prestable_category PS) ->
    Q PS.
Proof.
  intros PS H_left_op H_tri1_op.
  rewrite <- H_invol.
  destruct (H_dual (opposite_prestable_category PS)) as [H_forward _].
  apply H_forward.
  apply H_theorem; assumption.
Defined.

Theorem theorem_doubling_principle_final
  (P : PreStableCategory -> Type)
  (Q : PreStableCategory -> Type)
  (H_dual : forall PS, EquivT (P PS) (Q (opposite_prestable_category PS)))
  (H_theorem : forall PS, is_left_semi_stable PS -> satisfies_triangle_1 PS -> P PS)
  (H_invol : forall PS, opposite_prestable_category (opposite_prestable_category PS) = PS)
  : forall PS, is_right_semi_stable PS -> satisfies_triangle_2 PS -> Q PS.
Proof.
  intros PS H_right H_tri2.
  apply theorem_doubling_principle_correct with (P := P).
  - exact H_dual.
  - exact H_theorem.
  - exact H_invol.
  - apply right_stable_gives_opposite_left.
    exact H_right.
  - destruct (triangle_identity_duality (opposite_prestable_category PS)) as [_ H_back].
    pose proof H_tri2 as H_tri2'.
    rewrite <- H_invol in H_tri2'.
    exact (H_back H_tri2').
Defined.

Definition sample_category : PreStableCategory :=
  {| ps_tag := 7;
     ps_shift := 4;
     ps_Susp := fun x => x + 10;
     ps_Loop := fun x => x + 3;
     ps_eta := fun x => x + 20;
     ps_epsilon := fun x => x + 5 |}.

Definition sample_right_stable : is_right_semi_stable sample_category.
Proof.
  refine {| rsw_seed := 6; rsw_value := 11 |}.
  reflexivity.
Defined.

Definition sample_triangle2 : satisfies_triangle_2 sample_category.
Proof.
  refine {| t2_seed := 8; t2_value := 16 |}.
  reflexivity.
Defined.

Definition sample_right_property : RightProperty sample_category :=
  theorem_doubling_principle_final
    LeftProperty
    RightProperty
    dual_property_equiv
    sample_left_property
    double_opposite_involutive
    sample_category
    sample_right_stable
    sample_triangle2.

Definition sample_opposite_tag : nat :=
  ps_tag (opposite_prestable_category sample_category).

Definition sample_opposite_loop_value : nat :=
  ps_Loop (opposite_prestable_category sample_category) 5.

Definition sample_result_seed : nat :=
  rp_seed sample_right_property.

Definition sample_result_value : nat :=
  rp_value sample_right_property.

Definition sample_result_tag : nat :=
  rp_tag sample_right_property.

Definition sample_checksum : nat :=
  sample_opposite_tag +
  sample_opposite_loop_value +
  sample_result_seed +
  sample_result_value +
  sample_result_tag.

End OppositePropertyTransferTraceCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "opposite_property_transfer_trace" OppositePropertyTransferTraceCase.
