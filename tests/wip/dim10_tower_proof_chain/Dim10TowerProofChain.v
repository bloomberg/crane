(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: graded Goodwillie tower record together with concrete stabilization witnesses. *)

From Stdlib Require Import Nat.

Module Dim10TowerProofChainCase.

Definition ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
  match p with
  | eq_refl => eq_refl
  end.

Fixpoint nat_lt (n m : nat) : Type :=
  match n, m with
  | _, O => Empty_set
  | O, S _ => unit
  | S n', S m' => nat_lt n' m'
  end.

Fixpoint nat_le (n m : nat) : Type :=
  match n, m with
  | O, _ => unit
  | S _, O => Empty_set
  | S n', S m' => nat_le n' m'
  end.

Lemma nat_le_of_lt (n m : nat)
  : nat_lt n m -> nat_le n m.
Proof.
  revert m.
  induction n.
  - intros m _.
    destruct m.
    + exact tt.
    + exact tt.
  - intros m Hlt.
    destruct m.
    + destruct Hlt.
    + exact (IHn m Hlt).
Defined.

Record QPos : Type := {
  qpos_num : nat;
  qpos_denom_pred : nat
}.

Definition qpos_denom (q : QPos) : nat := S (qpos_denom_pred q).

Definition qpos_is_zero (q : QPos) : Type := qpos_num q = O.

Definition nat_to_qpos (n : nat) : QPos :=
  {| qpos_num := n; qpos_denom_pred := O |}.

Definition EventuallyZero (measure : nat -> QPos) : Type :=
  { N : nat & forall m, nat_lt N m -> qpos_is_zero (measure m) }.

Definition IsIntegerValued (measure : nat -> QPos) : Type :=
  forall n, qpos_denom_pred (measure n) = O.

Record GradedObj : Type := {
  go_dim : nat
}.

Definition go_zero : GradedObj := {| go_dim := O |}.

Fixpoint nat_sub (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S n', O => S n'
  | S n', S m' => nat_sub n' m'
  end.

Definition poly_approx_dim (base_dim n : nat) : nat := nat_sub base_dim n.

Definition layer_dim (base_dim n : nat) : nat :=
  nat_sub (poly_approx_dim base_dim n) (poly_approx_dim base_dim (S n)).

Definition layer_obj (base_dim n : nat) : GradedObj :=
  {| go_dim := layer_dim base_dim n |}.

Lemma nat_sub_zero_r (n : nat) : nat_sub n O = n.
Proof.
  destruct n.
  - reflexivity.
  - reflexivity.
Defined.

Lemma nat_sub_self (n : nat) : nat_sub n n = O.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    exact IHn.
Defined.

Definition layer_measure (base_dim n : nat) : QPos :=
  nat_to_qpos (layer_dim base_dim n).

Lemma layer_measure_is_integer (base_dim n : nat)
  : qpos_denom_pred (layer_measure base_dim n) = O.
Proof.
  reflexivity.
Defined.

Lemma layer_measure_eventually_zero (base_dim : nat)
  : EventuallyZero (layer_measure base_dim).
Proof.
  exists base_dim.
  intros m Hm.
  unfold qpos_is_zero, layer_measure, nat_to_qpos.
  simpl.
  unfold layer_dim, poly_approx_dim.
  revert m Hm.
  induction base_dim.
  - intros m _.
    reflexivity.
  - intros m Hlt.
    destruct m.
    + destruct Hlt.
    + simpl.
      exact (IHbase_dim m Hlt).
Defined.

Definition P_n_obj (n : nat) (X : GradedObj) : GradedObj :=
  {| go_dim := poly_approx_dim (go_dim X) n |}.

Definition D_n_obj (base_dim n : nat) : GradedObj :=
  layer_obj base_dim n.

Definition D_n_measure (base_dim n : nat) : QPos :=
  layer_measure base_dim n.

Lemma D_n_measure_eventually_zero (base_dim : nat)
  : EventuallyZero (D_n_measure base_dim).
Proof.
  exact (layer_measure_eventually_zero base_dim).
Defined.

Lemma D_n_measure_is_integer (base_dim : nat)
  : IsIntegerValued (D_n_measure base_dim).
Proof.
  exact (layer_measure_is_integer base_dim).
Defined.

Record GradedGoodwillieTower (base_dim : nat) := {
  ggt_P : nat -> GradedObj;
  ggt_P_def : forall n, ggt_P n = P_n_obj n {| go_dim := base_dim |};
  ggt_D : nat -> GradedObj;
  ggt_D_def : forall n, ggt_D n = D_n_obj base_dim n
}.

Definition make_graded_goodwillie_tower (base_dim : nat)
  : GradedGoodwillieTower base_dim.
Proof.
  refine
    {| ggt_P := fun n => P_n_obj n {| go_dim := base_dim |};
       ggt_D := fun n => D_n_obj base_dim n |}.
  - intro n.
    reflexivity.
  - intro n.
    reflexivity.
Defined.

Theorem graded_goodwillie_layers_stabilize (base_dim : nat)
  : { N : nat & forall n, nat_lt N n -> go_dim (D_n_obj base_dim n) = O }.
Proof.
  destruct (D_n_measure_eventually_zero base_dim) as [N HN].
  exists N.
  intros n Hn.
  pose proof (HN n Hn) as Hzero.
  exact Hzero.
Defined.

Lemma nat_sub_zero_when_le (d n : nat)
  : nat_le d n -> nat_sub d n = O.
Proof.
  revert n.
  induction d.
  - intros n _.
    reflexivity.
  - intros n Hle.
    destruct n.
    + destruct Hle.
    + simpl.
      exact (IHd n Hle).
Defined.

Theorem graded_goodwillie_P_stabilizes (base_dim : nat)
  : { N : nat & forall n, nat_lt N n -> P_n_obj n {| go_dim := base_dim |} = go_zero }.
Proof.
  exists base_dim.
  intros n Hn.
  unfold P_n_obj, poly_approx_dim, go_zero.
  simpl.
  apply ap.
  apply nat_sub_zero_when_le.
  apply nat_le_of_lt.
  exact Hn.
Defined.

Definition dim10_tower : GradedGoodwillieTower 10 :=
  make_graded_goodwillie_tower 10.

Theorem dim10_layers_stabilize
  : { N : nat & forall n, nat_lt N n -> go_dim (ggt_D 10 dim10_tower n) = O }.
Proof.
  destruct (graded_goodwillie_layers_stabilize 10) as [N HN].
  exists N.
  intros n Hn.
  rewrite (ggt_D_def 10 dim10_tower n).
  exact (HN n Hn).
Defined.

Theorem dim10_P_stabilizes
  : { N : nat & forall n, nat_lt N n -> ggt_P 10 dim10_tower n = go_zero }.
Proof.
  destruct (graded_goodwillie_P_stabilizes 10) as [N HN].
  exists N.
  intros n Hn.
  rewrite (ggt_P_def 10 dim10_tower n).
  exact (HN n Hn).
Defined.

Theorem graded_complete_proof_chain (base_dim : nat)
  : (IsIntegerValued (D_n_measure base_dim)) *
    (EventuallyZero (D_n_measure base_dim)) *
    ({ N : nat & forall n, nat_lt N n -> go_dim (D_n_obj base_dim n) = O }) *
    ({ N : nat & forall n, nat_lt N n -> P_n_obj n {| go_dim := base_dim |} = go_zero }).
Proof.
  exact
    (((D_n_measure_is_integer base_dim,
       D_n_measure_eventually_zero base_dim),
      graded_goodwillie_layers_stabilize base_dim),
     graded_goodwillie_P_stabilizes base_dim).
Defined.

Record GoodwillieProofChain (base_dim : nat) := {
  gc_integer : IsIntegerValued (D_n_measure base_dim);
  gc_eventually_zero : EventuallyZero (D_n_measure base_dim);
  gc_layers_stabilize : { N : nat & forall n, nat_lt N n -> go_dim (D_n_obj base_dim n) = O };
  gc_P_stabilize : { N : nat & forall n, nat_lt N n -> P_n_obj n {| go_dim := base_dim |} = go_zero }
}.

Definition make_goodwillie_proof_chain (base_dim : nat)
  : GoodwillieProofChain base_dim.
Proof.
  refine
    {| gc_integer := D_n_measure_is_integer base_dim;
       gc_eventually_zero := D_n_measure_eventually_zero base_dim;
       gc_layers_stabilize := graded_goodwillie_layers_stabilize base_dim;
       gc_P_stabilize := graded_goodwillie_P_stabilizes base_dim |}.
Defined.

Definition dim10_chain : GoodwillieProofChain 10 :=
  make_goodwillie_proof_chain 10.

Definition dim10_pair_chain :=
  graded_complete_proof_chain 10.

Record Dim10Bundle : Type := {
  dt_tower : GradedGoodwillieTower 10;
  dt_chain : GoodwillieProofChain 10
}.

Definition dim10_bundle : Dim10Bundle :=
  {| dt_tower := dim10_tower;
     dt_chain := dim10_chain |}.

Definition dim10_p0_dim : nat :=
  go_dim (ggt_P 10 (dt_tower dim10_bundle) 0).

Definition dim10_p4_dim : nat :=
  go_dim (ggt_P 10 (dt_tower dim10_bundle) 4).

Definition dim10_p9_dim : nat :=
  go_dim (ggt_P 10 (dt_tower dim10_bundle) 9).

Definition dim10_p10_dim : nat :=
  go_dim (ggt_P 10 (dt_tower dim10_bundle) 10).

Definition dim10_p12_dim : nat :=
  go_dim (ggt_P 10 (dt_tower dim10_bundle) 12).

Definition dim10_d0_dim : nat :=
  go_dim (ggt_D 10 (dt_tower dim10_bundle) 0).

Definition dim10_d4_dim : nat :=
  go_dim (ggt_D 10 (dt_tower dim10_bundle) 4).

Definition dim10_d9_dim : nat :=
  go_dim (ggt_D 10 (dt_tower dim10_bundle) 9).

Definition dim10_d10_dim : nat :=
  go_dim (ggt_D 10 (dt_tower dim10_bundle) 10).

Definition dim10_layers_cutoff : nat :=
  match gc_layers_stabilize 10 (dt_chain dim10_bundle) with
  | existT _ N _ => N
  end.

Definition dim10_P_cutoff : nat :=
  match gc_P_stabilize 10 (dt_chain dim10_bundle) with
  | existT _ N _ => N
  end.

Definition dim10_layers_cutoff_matches : bool :=
  Nat.eqb dim10_layers_cutoff 10.

Definition dim10_P_cutoff_matches : bool :=
  Nat.eqb dim10_P_cutoff 10.

Definition dim10_dimension_checksum : nat :=
  dim10_p0_dim + dim10_p4_dim + dim10_p9_dim + dim10_p10_dim +
  dim10_d0_dim + dim10_d4_dim + dim10_d9_dim + dim10_d10_dim +
  dim10_layers_cutoff + dim10_P_cutoff.

End Dim10TowerProofChainCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "dim10_tower_proof_chain" Dim10TowerProofChainCase.
