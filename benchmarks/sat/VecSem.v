(** Layer 0 of the solver's proof: what the [vecE] events mean, and how to
    reason about the trees that perform them.

    A heap maps locations to cells, and a cell is a list at some element
    type.  The events are given a {i relational} semantics, [step], rather
    than a handler: a handler would have to compare types to answer
    [VGet {A}], while a relation fixes [A] by its pattern.  [runs] is the
    finite unfolding of a tree against the heap, and [wp] the partial
    correctness it supports: every run that finishes satisfies the
    postcondition.  A run that aborts, or performs an event no step allows,
    never finishes, so it satisfies every [wp] vacuously. *)
From Stdlib Require Import List PeanoNat Lia Eqdep.
From Crane Require Import Monads.ITree.
Require Import SatVec.
Import ListNotations.

Definition cell := {A : Type & list A}.
Definition heap := loc -> option cell.

Definition upd (h : heap) (l : loc) (c : cell) : heap :=
  fun l' => if Nat.eqb l' l then Some c else h l'.

Lemma upd_eq h l c : upd h l c l = Some c.
Proof. unfold upd. now rewrite Nat.eqb_refl. Qed.

Lemma upd_neq h l c l' : l' <> l -> upd h l c l' = h l'.
Proof. intros. unfold upd. now rewrite (proj2 (Nat.eqb_neq _ _) H). Qed.

(** [xs] with position [i] replaced by [x]. *)
Fixpoint lset {A} (xs : list A) (i : nat) (x : A) : list A :=
  match xs, i with
  | [], _ => []
  | _ :: xs', O => x :: xs'
  | y :: xs', S i' => y :: lset xs' i' x
  end.

Lemma lset_length {A} (xs : list A) i x : length (lset xs i x) = length xs.
Proof. revert i; induction xs; destruct i; cbn; auto. Qed.

(** One event against the heap: the answer it may give and the heap it
    leaves.  Indices must be in bounds and handles must point at a cell of
    the event's element type; [VAbort] has no step at all. *)
Definition step {X} (h : heap) (e : vecE X) : X -> heap -> Prop :=
  match e in vecE X return X -> heap -> Prop with
  | @VMake A n x => fun v h' =>
      h (vloc v) = None /\ h' = upd h (vloc v) (existT _ A (repeat x n))
  | @VGet A v i => fun x h' =>
      h' = h /\ exists xs, h (vloc v) = Some (existT _ A xs) /\ nth_error xs i = Some x
  | @VSet A v i x => fun _ h' =>
      exists xs, h (vloc v) = Some (existT _ A xs) /\ i < length xs /\
                 h' = upd h (vloc v) (existT _ A (lset xs i x))
  | @VLen A v => fun n h' =>
      h' = h /\ exists xs, h (vloc v) = Some (existT _ A xs) /\ n = length xs
  | @VPush A v x => fun _ h' =>
      exists xs, h (vloc v) = Some (existT _ A xs) /\
                 h' = upd h (vloc v) (existT _ A (xs ++ [x]))
  | @VShrink A v n => fun _ h' =>
      exists xs, h (vloc v) = Some (existT _ A xs) /\ n <= length xs /\
                 h' = upd h (vloc v) (existT _ A (firstn n xs))
  | VAbort _ => fun _ _ => False
  end.

(** [runs h t r h']: [t], started in [h], finishes with [r] in [h'] after
    finitely many steps. *)
Inductive runs {R} : heap -> itree vecE R -> R -> heap -> Prop :=
| RunRet h t r : observe t = RetF r -> runs h t r h
| RunTau h t t' r h' : observe t = TauF t' -> runs h t' r h' -> runs h t r h'
| RunVis h t X (e : vecE X) k x h1 r h' :
    observe t = VisF e k -> step h e x h1 -> runs h1 (k x) r h' -> runs h t r h'.

Definition wp {R} (t : itree vecE R) (Q : R -> heap -> Prop) (h : heap) : Prop :=
  forall r h', runs h t r h' -> Q r h'.

(** ** Structural rules *)

Lemma observe_bind {E T U} (t : itree E T) (k : T -> itree E U) :
  observe (ITree.bind t k) =
  match observe t with
  | RetF r => observe (k r)
  | TauF t' => TauF (ITree.bind t' k)
  | VisF e h => VisF e (fun x => ITree.bind (h x) k)
  end.
Proof. unfold ITree.bind, ITree.subst, observe. cbn. destruct (_observe t); reflexivity. Qed.

Lemma runs_bind {T U} h (t : itree vecE T) (k : T -> itree vecE U) r h' :
  runs h (ITree.bind t k) r h' ->
  exists r1 h1, runs h t r1 h1 /\ runs h1 (k r1) r h'.
Proof.
  intros Hr. remember (ITree.bind t k) as tb eqn:E. revert t E.
  induction Hr as [h tb r Ho | h tb t' r h' Ho Hr IH | h tb X e k' x h1 r h' Ho Hs Hr IH];
    intros t ->; rewrite observe_bind in Ho; destruct (observe t) eqn:Et;
    try discriminate.
  - exists r0, h. split; [now constructor | now constructor].
  - exists r0, h. split; [now constructor | eapply RunTau; eauto].
  - injection Ho as <-. destruct (IH t0 eq_refl) as (r1 & h2 & H1 & H2).
    exists r1, h2. split; [eapply RunTau; eauto | exact H2].
  - exists r0, h. split; [now constructor | eapply RunVis; eauto].
  - injection Ho as -> He Hk. apply inj_pair2 in He, Hk. subst.
    destruct (IH (k0 x) eq_refl) as (r1 & h2 & H1 & H2).
    exists r1, h2. split; [eapply RunVis; eauto | exact H2].
Qed.

Lemma wp_bind {T U} (t : itree vecE T) (k : T -> itree vecE U) Q h :
  wp t (fun r h1 => wp (k r) Q h1) h -> wp (ITree.bind t k) Q h.
Proof.
  intros Ht r h' Hr. destruct (runs_bind _ _ _ _ _ Hr) as (r1 & h1 & H1 & H2).
  exact (Ht _ _ H1 _ _ H2).
Qed.

Lemma wp_ret {R} (x : R) (Q : R -> heap -> Prop) h : Q x h -> wp (Ret x) Q h.
Proof. intros HQ r h' Hr. inversion Hr; subst; cbn in *; try discriminate. congruence. Qed.

Lemma wp_conseq {R} (t : itree vecE R) (Q Q' : R -> heap -> Prop) h :
  wp t Q h -> (forall r h', Q r h' -> Q' r h') -> wp t Q' h.
Proof. intros H HQ r h' Hr. exact (HQ _ _ (H _ _ Hr)). Qed.

(** A tree that leaves the heap alone can be followed by anything that
    holds of the heap it started in. *)
Lemma wp_readonly {R} (t : itree vecE R) (Q : R -> heap -> Prop) h :
  wp t (fun _ h' => h' = h) h -> (forall r, Q r h) -> wp t Q h.
Proof. intros H HQ r h' Hr. rewrite (H _ _ Hr). apply HQ. Qed.

(** ** Events *)

(** A tree that is one event and its answer: what the smart constructors
    [vmake], [vget], ... unfold to. *)
Lemma wp_trigger {X} (t : itree vecE X) (e : vecE X) (Q : X -> heap -> Prop) h :
  observe t = VisF e (fun x => go (RetF x)) ->
  (forall x h', step h e x h' -> Q x h') ->
  wp t Q h.
Proof.
  intros Ht HQ r h' Hr. inversion Hr; subst; rewrite Ht in H; try discriminate.
  injection H as -> He Hk. apply inj_pair2 in He, Hk. subst.
  inversion H1; subst; cbn in *; try discriminate.
  injection H as ->. now apply HQ.
Qed.

Section Events.
Context {A : Type}.

Lemma wp_vmake n (x : A) (Q : vec A -> heap -> Prop) h :
  (forall v, h (vloc v) = None -> Q v (upd h (vloc v) (existT _ A (repeat x n)))) ->
  wp (vmake (E := vecE) n x) Q h.
Proof. intros HQ. apply wp_trigger with (e := VMake n x); [reflexivity |]. intros v h' [Hn ->]. auto. Qed.

Lemma wp_vget (v : vec A) i (Q : A -> heap -> Prop) h :
  (forall xs x, h (vloc v) = Some (existT _ A xs) -> nth_error xs i = Some x -> Q x h) ->
  wp (vget (E := vecE) v i) Q h.
Proof. intros HQ. apply wp_trigger with (e := VGet v i); [reflexivity |]. intros x h' [-> (xs & Hv & Hi)]. eauto. Qed.

Lemma wp_vset (v : vec A) i (x : A) (Q : unit -> heap -> Prop) h :
  (forall xs, h (vloc v) = Some (existT _ A xs) -> i < length xs ->
     Q tt (upd h (vloc v) (existT _ A (lset xs i x)))) ->
  wp (vset (E := vecE) v i x) Q h.
Proof. intros HQ. apply wp_trigger with (e := VSet v i x); [reflexivity |]. intros [] h' (xs & Hv & Hi & ->). auto. Qed.

Lemma wp_vlen (v : vec A) (Q : nat -> heap -> Prop) h :
  (forall xs, h (vloc v) = Some (existT _ A xs) -> Q (length xs) h) ->
  wp (vlen (E := vecE) v) Q h.
Proof. intros HQ. apply wp_trigger with (e := VLen v); [reflexivity |]. intros n h' [-> (xs & Hv & ->)]. auto. Qed.

Lemma wp_vpush (v : vec A) (x : A) (Q : unit -> heap -> Prop) h :
  (forall xs, h (vloc v) = Some (existT _ A xs) ->
     Q tt (upd h (vloc v) (existT _ A (xs ++ [x])))) ->
  wp (vpush (E := vecE) v x) Q h.
Proof. intros HQ. apply wp_trigger with (e := VPush v x); [reflexivity |]. intros [] h' (xs & Hv & ->). auto. Qed.

Lemma wp_vshrink (v : vec A) n (Q : unit -> heap -> Prop) h :
  (forall xs, h (vloc v) = Some (existT _ A xs) -> n <= length xs ->
     Q tt (upd h (vloc v) (existT _ A (firstn n xs)))) ->
  wp (vshrink (E := vecE) v n) Q h.
Proof. intros HQ. apply wp_trigger with (e := VShrink v n); [reflexivity |]. intros [] h' (xs & Hv & Hn & ->). auto. Qed.

Lemma wp_vabort site (Q : A -> heap -> Prop) h : wp (vabort (E := vecE) site) Q h.
Proof. apply wp_trigger with (e := VAbort site); [reflexivity | intros _ _ []]. Qed.

End Events.

(** Two cells at the same location and type hold the same list. *)
Lemma cell_inj {A} (h : heap) (l : loc) (xs ys : list A) :
  h l = Some (existT _ A xs) -> h l = Some (existT _ A ys) -> xs = ys.
Proof. intros H1 H2. rewrite H1 in H2. injection H2 as H2. now apply inj_pair2 in H2. Qed.
