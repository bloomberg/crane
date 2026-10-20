(** Safety for [vecE] programs: no run gets stuck.

    [wp] in [VecSem] is partial correctness: a run that performs an event
    no [step] allows (an index out of bounds, a dangling handle) has no
    [runs] derivation, so it satisfies every [wp] vacuously.  [safe t Q h]
    rules that out.  Every configuration [t] reaches from [h] is either
    finished, with an answer satisfying [Q], or about to perform an event
    that has a step -- or about to give up with [VAbort], the one event that
    is allowed to have none (it is the extracted code's intended "out of
    fuel" exit).  Termination is not claimed.

    Allocation needs a free location, so safety is only claimed from finite
    heaps; every step keeps a heap finite, so this is assumed once, at the
    start, and never mentioned again. *)
From Stdlib Require Import List PeanoNat Lia Eqdep.
From Crane Require Import Monads.ITree.
Require Import SatVec VecSem.
Import ListNotations.

(** [reach h t h' t']: [t], started in [h], gets to [t'] in [h'] after
    finitely many steps. *)
Inductive reach {R} : heap -> itree vecE R -> heap -> itree vecE R -> Prop :=
| ReachRefl h t : reach h t h t
| ReachTau h t t' h' u : observe t = TauF t' -> reach h t' h' u -> reach h t h' u
| ReachVis h t X (e : vecE X) k x h1 h' u :
    observe t = VisF e k -> step h e x h1 -> reach h1 (k x) h' u -> reach h t h' u.

Definition is_abort {X} (e : vecE X) : Prop := match e with VAbort _ => True | _ => False end.

(** A configuration that is not stuck. *)
Definition ok_at {R} (Q : R -> heap -> Prop) (h : heap) (t : itree vecE R) : Prop :=
  match observe t with
  | RetF r => Q r h
  | TauF _ => True
  | VisF e _ => is_abort e \/ exists x h', step h e x h'
  end.

(** Only finitely many locations are allocated. *)
Definition fin (h : heap) : Prop := exists N, forall l, N <= l -> h l = None.

Definition safe {R} (t : itree vecE R) (Q : R -> heap -> Prop) (h : heap) : Prop :=
  fin h -> forall h' u, reach h t h' u -> ok_at Q h' u.

(** ** Finite heaps *)

Lemma fin_upd h l c : fin h -> fin (upd h l c).
Proof.
  intros [N HN]. exists (max N (S l)). intros l' Hl. unfold upd.
  destruct (Nat.eqb_spec l' l); [lia | apply HN; lia].
Qed.

Lemma fin_step {X} h (e : vecE X) x h' : fin h -> step h e x h' -> fin h'.
Proof.
  intros Hf Hs. destruct e; cbn in Hs.
  - destruct Hs as [_ ->]. now apply fin_upd.
  - now destruct Hs as [-> _].
  - destruct Hs as (xs & _ & _ & ->). now apply fin_upd.
  - now destruct Hs as [-> _].
  - destruct Hs as (xs & _ & ->). now apply fin_upd.
  - destruct Hs as (xs & _ & _ & ->). now apply fin_upd.
  - destruct Hs.
Qed.

Lemma fin_reach {R} h (t : itree vecE R) h' u : fin h -> reach h t h' u -> fin h'.
Proof. intros Hf Hr. induction Hr; eauto using fin_step. Qed.

Lemma fin_runs {R} h (t : itree vecE R) r h' : fin h -> runs h t r h' -> fin h'.
Proof. intros Hf Hr. induction Hr; eauto using fin_step. Qed.

(** ** Safety and partial correctness *)

Lemma runs_reach {R} h (t : itree vecE R) r h' :
  runs h t r h' -> exists u, reach h t h' u /\ observe u = RetF r.
Proof.
  induction 1 as [h t r Ho | h t t' r h' Ho _ (u & Hr & Hu) | h t X e k x h1 r h' Ho Hs _ (u & Hr & Hu)].
  - exists t. split; [constructor | exact Ho].
  - exists u. split; [eapply ReachTau; eauto | exact Hu].
  - exists u. split; [eapply ReachVis; eauto | exact Hu].
Qed.

Lemma safe_runs {R} (t : itree vecE R) Q h r h' : safe t Q h -> fin h -> runs h t r h' -> Q r h'.
Proof.
  intros Hs Hf Hr. destruct (runs_reach _ _ _ _ Hr) as (u & Hu & Ho).
  specialize (Hs Hf _ _ Hu). unfold ok_at in Hs. now rewrite Ho in Hs.
Qed.

(** A safe program is partially correct. *)
Lemma safe_wp {R} (t : itree vecE R) Q h : safe t Q h -> fin h -> wp t Q h.
Proof. intros Hs Hf r h' Hr. eapply safe_runs; eauto. Qed.

Lemma reach_runs {R} h (t : itree vecE R) h' u r :
  reach h t h' u -> observe u = RetF r -> runs h t r h'.
Proof.
  intros Hr Hu. induction Hr.
  - now constructor.
  - eapply RunTau; eauto.
  - eapply RunVis; eauto.
Qed.

(** Safety and partial correctness, proved apart, combine. *)
Lemma safe_and_wp {R} (t : itree vecE R) (P Q : R -> heap -> Prop) h :
  safe t P h -> wp t Q h -> safe t (fun r h' => P r h' /\ Q r h') h.
Proof.
  intros Hs Hw Hf h' u Hr. specialize (Hs Hf h' u Hr). unfold ok_at in *.
  destruct (observe u) eqn:E; auto. split; [exact Hs|].
  apply Hw. eapply reach_runs; eauto.
Qed.

(** ** Structural rules *)

Lemma reach_bind {T U} h (t : itree vecE T) (k : T -> itree vecE U) h' u :
  reach h (ITree.bind t k) h' u ->
  (exists t1, reach h t h' t1 /\ u = ITree.bind t1 k) \/
  (exists r h1, runs h t r h1 /\ reach h1 (k r) h' u).
Proof.
  intros Hr. remember (ITree.bind t k) as tb eqn:E. revert t E.
  induction Hr as [h tb | h tb t' h' u Ho Hr IH | h tb X e k' x h1 h' u Ho Hs Hr IH];
    intros t ->.
  - left. exists t. split; [constructor | reflexivity].
  - rewrite observe_bind in Ho. destruct (observe t) eqn:Et; try discriminate.
    + right. exists r, h. split; [now constructor | eapply ReachTau; eauto].
    + injection Ho as <-. destruct (IH t0 eq_refl) as [(t1 & H1 & ->) | (r & h2 & H1 & H2)].
      * left. exists t1. split; [eapply ReachTau; eauto | reflexivity].
      * right. exists r, h2. split; [eapply RunTau; eauto | exact H2].
  - rewrite observe_bind in Ho. destruct (observe t) eqn:Et; try discriminate.
    + right. exists r, h. split; [now constructor | eapply ReachVis; eauto].
    + injection Ho as -> He Hk. apply inj_pair2 in He, Hk. subst.
      destruct (IH (k0 x) eq_refl) as [(t1 & H1 & ->) | (r & h2 & H1 & H2)].
      * left. exists t1. split; [eapply ReachVis; eauto | reflexivity].
      * right. exists r, h2. split; [eapply RunVis; eauto | exact H2].
Qed.

Lemma safe_bind {T U} (t : itree vecE T) (k : T -> itree vecE U) Q h :
  safe t (fun r h1 => safe (k r) Q h1) h -> safe (ITree.bind t k) Q h.
Proof.
  intros Hs Hf h' u Hr. destruct (reach_bind _ _ _ _ _ Hr) as [(t1 & H1 & ->) | (r & h1 & H1 & H2)].
  - pose proof (Hs Hf _ _ H1) as Ho. pose proof (fin_reach _ _ _ _ Hf H1) as Hf'.
    unfold ok_at in *. rewrite observe_bind. destruct (observe t1) eqn:E; auto.
    specialize (Ho Hf' _ _ (ReachRefl _ _)). exact Ho.
  - eapply (safe_runs _ _ _ _ _ Hs Hf H1); [eapply fin_runs; eauto | exact H2].
Qed.

Lemma safe_seq {T U} (t : itree vecE T) (k : T -> itree vecE U) P Q h :
  safe t P h -> (forall r h1, P r h1 -> safe (k r) Q h1) -> safe (ITree.bind t k) Q h.
Proof.
  intros Ht Hk. apply safe_bind. intros Hf h' u Hr. specialize (Ht Hf h' u Hr).
  unfold ok_at in *. destruct (observe u); auto.
Qed.

Lemma safe_ret {R} (x : R) (Q : R -> heap -> Prop) h : Q x h -> safe (Ret x) Q h.
Proof.
  intros HQ _ h' u Hr. inversion Hr; subst; cbn in *; try discriminate. exact HQ.
Qed.

Lemma safe_conseq {R} (t : itree vecE R) (Q Q' : R -> heap -> Prop) h :
  safe t Q h -> (forall r h', Q r h' -> Q' r h') -> safe t Q' h.
Proof.
  intros Hs HQ Hf h' u Hr. specialize (Hs Hf h' u Hr). unfold ok_at in *.
  destruct (observe u); auto.
Qed.

(** ** Events *)

Lemma safe_trigger {X} (t : itree vecE X) (e : vecE X) (Q : X -> heap -> Prop) h :
  observe t = VisF e (fun x => go (RetF x)) ->
  (fin h -> exists x h', step h e x h') ->
  (forall x h', step h e x h' -> Q x h') ->
  safe t Q h.
Proof.
  intros Ht Hex HQ Hf h' u Hr. inversion Hr; subst.
  - unfold ok_at. rewrite Ht. right. auto.
  - rewrite Ht in H. discriminate.
  - rewrite Ht in H. injection H as -> He Hk. apply inj_pair2 in He, Hk. subst.
    inversion H1; subst; cbn in *; try discriminate. unfold ok_at. cbn. auto.
Qed.

Lemma safe_vabort {A} site (Q : A -> heap -> Prop) h : safe (vabort (E := vecE) site) Q h.
Proof.
  intros _ h' u Hr. inversion Hr; subst.
  - unfold ok_at. cbn. left. exact I.
  - cbn in H. discriminate.
  - cbn in H. injection H as -> He Hk. apply inj_pair2 in He. subst. destruct H0.
Qed.

Section Events.
Context {A : Type}.

Lemma safe_vmake n (x : A) (Q : vec A -> heap -> Prop) h :
  (forall v, h (vloc v) = None -> Q v (upd h (vloc v) (existT _ A (repeat x n)))) ->
  safe (vmake (E := vecE) n x) Q h.
Proof.
  intros HQ. apply safe_trigger with (e := VMake n x); [reflexivity | |].
  - intros [N HN]. exists (mk_vec N), (upd h N (existT _ A (repeat x n))). cbn.
    split; [apply HN; lia | reflexivity].
  - intros v h' [Hn ->]. auto.
Qed.

Lemma safe_vget (v : vec A) i xs (Q : A -> heap -> Prop) h :
  h (vloc v) = Some (existT _ A xs) -> i < length xs ->
  (forall x, nth_error xs i = Some x -> Q x h) ->
  safe (vget (E := vecE) v i) Q h.
Proof.
  intros Hv Hi HQ. apply safe_trigger with (e := VGet v i); [reflexivity | |].
  - intros _. destruct (nth_error xs i) as [x|] eqn:E; [| apply nth_error_None in E; lia].
    exists x, h. split; [reflexivity | eauto].
  - intros x h' [-> (ys & Hy & Hx)]. rewrite (cell_inj _ _ _ _ Hy Hv) in Hx. auto.
Qed.

Lemma safe_vset (v : vec A) i (x : A) xs (Q : unit -> heap -> Prop) h :
  h (vloc v) = Some (existT _ A xs) -> i < length xs ->
  Q tt (upd h (vloc v) (existT _ A (lset xs i x))) ->
  safe (vset (E := vecE) v i x) Q h.
Proof.
  intros Hv Hi HQ. apply safe_trigger with (e := VSet v i x); [reflexivity | |].
  - intros _. exists tt, (upd h (vloc v) (existT _ A (lset xs i x))). cbn. eauto.
  - intros [] h' (ys & Hy & _ & ->). now rewrite (cell_inj _ _ _ _ Hy Hv).
Qed.

Lemma safe_vlen (v : vec A) xs (Q : nat -> heap -> Prop) h :
  h (vloc v) = Some (existT _ A xs) -> Q (length xs) h -> safe (vlen (E := vecE) v) Q h.
Proof.
  intros Hv HQ. apply safe_trigger with (e := VLen v); [reflexivity | |].
  - intros _. exists (length xs), h. cbn. eauto.
  - intros n h' [-> (ys & Hy & ->)]. now rewrite (cell_inj _ _ _ _ Hy Hv).
Qed.

Lemma safe_vpush (v : vec A) (x : A) xs (Q : unit -> heap -> Prop) h :
  h (vloc v) = Some (existT _ A xs) ->
  Q tt (upd h (vloc v) (existT _ A (xs ++ [x]))) ->
  safe (vpush (E := vecE) v x) Q h.
Proof.
  intros Hv HQ. apply safe_trigger with (e := VPush v x); [reflexivity | |].
  - intros _. exists tt, (upd h (vloc v) (existT _ A (xs ++ [x]))). cbn. eauto.
  - intros [] h' (ys & Hy & ->). now rewrite (cell_inj _ _ _ _ Hy Hv).
Qed.

Lemma safe_vshrink (v : vec A) n xs (Q : unit -> heap -> Prop) h :
  h (vloc v) = Some (existT _ A xs) -> n <= length xs ->
  Q tt (upd h (vloc v) (existT _ A (firstn n xs))) ->
  safe (vshrink (E := vecE) v n) Q h.
Proof.
  intros Hv Hn HQ. apply safe_trigger with (e := VShrink v n); [reflexivity | |].
  - intros _. exists tt, (upd h (vloc v) (existT _ A (firstn n xs))). cbn. eauto.
  - intros [] h' (ys & Hy & _ & ->). now rewrite (cell_inj _ _ _ _ Hy Hv).
Qed.

End Events.
