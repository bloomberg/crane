(** What the solver's events mean, and how to reason about the trees that
    perform them.

    [Solver.E] has three kinds of event: [Global] events on [nat] cells
    ([Vn]), [Global] events on array cells ([Va]), and exceptions.  A heap
    is a pair of [Global] stores, the [Vn] one and the [Va] one, of the
    store type [Global.run] uses.  [step] gives the events a relational
    semantics through [GlobalFacts.hstep], the function version of
    [Global.handle]: a [Vn] event acts on the first store, a [Va] event on
    the second, exactly as the handler would, and an exception has no step.

    [safe t Q h] says that no configuration [t] reaches from [h] is stuck:
    each is finished with an answer satisfying [Q], or about to step, or
    about to throw [Solver.out_of_fuel]'s exception, the program's one
    sanctioned exit.  Termination is not claimed.  [safe_bind], [safe_ret]
    and one rule per operation, stated over the array contents predicate
    [arr] and the reference predicate [refp], are what the solver proofs
    walk programs with.

    [safe_model] is the bridge: from a safe tree, the two-layer run of
    [Global.interp] (first the [Vn] events, then the [Va] events) never
    fails except with "out of fuel", and every answer it returns satisfies
    [Q] on the final stores.  It is an instance, used twice, of the
    generic [rsafe_interp]: interpreting the [Global] events of a tree that
    is safe under a layered semantics gives a tree safe under the semantics
    of the remaining events. *)
From Stdlib Require Import PrimString List PeanoNat Lia Eqdep Classes.EquivDec.
From ExtLib Require Import Structures.Reducible.
From ITree Require Import ITree ITreeFacts Events.Exception.
From Crane Require Import Monads.ITree Monads.Error Monads.Indices Monads.Global
  Monads.GlobalFacts Utils.HAList Utils.HMap.
Require Import Solver Abstract.
Import ListNotations.

(** * Relational semantics of an effect

    For any effect [F] over a state [S]: [rstep] says what an event may
    answer and which state it leaves, and [allow] which events may be
    performed with no step (a sanctioned exit). *)
Section Rel.

  Context {F : Type -> Type} {S : Type}.
  Context (rstep : forall {X : Type}, S -> F X -> X -> S -> Prop).
  Context (allow : forall {X : Type}, F X -> Prop).
  Arguments rstep {X}. Arguments allow {X}.

  (** [rreach h t h' u]: [t], started in [h], gets to [u] in [h'] after
      finitely many steps. *)
  Inductive rreach {R} : S -> itree F R -> S -> itree F R -> Prop :=
  | RReachRefl h t : rreach h t h t
  | RReachTau h t t' h' u : observe t = TauF t' -> rreach h t' h' u -> rreach h t h' u
  | RReachVis h t X (e : F X) k x h1 h' u :
      observe t = VisF e k -> rstep h e x h1 -> rreach h1 (k x) h' u -> rreach h t h' u.

  (** A configuration that is not stuck: finished with an answer satisfying
      [Q], silent, or an event that is allowed or has a step. *)
  Definition rok {R} (Q : R -> S -> Prop) (h : S) (t : itree F R) : Prop :=
    match observe t with
    | RetF r => Q r h
    | TauF _ => True
    | VisF e _ => allow e \/ exists x h', rstep h e x h'
    end.

  (** Every configuration [t] reaches from [h] is not stuck, and a finished
      one satisfies [Q]. *)
  Definition rsafe {R} (t : itree F R) (Q : R -> S -> Prop) (h : S) : Prop :=
    forall h' u, rreach h t h' u -> rok Q h' u.

  (** One unfolding of [bind]. *)
  Lemma observe_bind {T U} (t : itree F T) (k : T -> itree F U) :
    observe (ITree.bind t k) =
    match observe t with
    | RetF r => observe (k r)
    | TauF t' => TauF (ITree.bind t' k)
    | VisF e h => VisF e (fun x => ITree.bind (h x) k)
    end.
  Proof. unfold ITree.bind, ITree.subst, observe. cbn. destruct (_observe t); reflexivity. Qed.

  (** A configuration reached from [ITree.bind t k] is either still inside
      [t], or inside [k] after [t] reached an answer. *)
  Lemma rreach_bind {T U} h (t : itree F T) (k : T -> itree F U) h' u :
    rreach h (ITree.bind t k) h' u ->
    (exists t1, rreach h t h' t1 /\ u = ITree.bind t1 k) \/
    (exists t1 r h1, rreach h t h1 t1 /\ observe t1 = RetF r /\ rreach h1 (k r) h' u).
  Proof.
    intros Hr. remember (ITree.bind t k) as tb eqn:Eb. revert t Eb.
    induction Hr as [h tb | h tb t' h' u Ho Hr IH | h tb X e k' x h1 h' u Ho Hs Hr IH];
      intros t ->.
    - left. exists t. split; [constructor | reflexivity].
    - rewrite observe_bind in Ho. destruct (observe t) as [r|t0|Y e k0] eqn:Et; try discriminate.
      + right. exists t, r, h. split; [constructor | split; [exact Et | eapply RReachTau; eauto]].
      + injection Ho as <-.
        destruct (IH t0 eq_refl) as [(t1 & H1 & ->) | (t1 & r & h2 & H1 & H2 & H3)].
        * left. exists t1. split; [eapply RReachTau; eauto | reflexivity].
        * right. exists t1, r, h2. split; [eapply RReachTau; eauto | auto].
    - rewrite observe_bind in Ho. destruct (observe t) as [r|t0|Y e0 k0] eqn:Et; try discriminate.
      + right. exists t, r, h. split; [constructor | split; [exact Et | eapply RReachVis; eauto]].
      + injection Ho as -> He Hk. apply inj_pair2 in He, Hk. subst.
        destruct (IH (k0 x) eq_refl) as [(t1 & H1 & ->) | (t1 & r & h2 & H1 & H2 & H3)].
        * left. exists t1. split; [eapply RReachVis; eauto | reflexivity].
        * right. exists t1, r, h2. split; [eapply RReachVis; eauto | auto].
  Qed.

  (** A safe tree's own configuration is not stuck. *)
  Lemma rsafe_ok {R} (t : itree F R) Q h : rsafe t Q h -> rok Q h t.
  Proof. intros Hs. apply Hs, RReachRefl. Qed.

  (** Safety survives a silent step. *)
  Lemma rsafe_tau_inv {R} (t t' : itree F R) Q h :
    observe t = TauF t' -> rsafe t Q h -> rsafe t' Q h.
  Proof. intros Ho Hs h' u Hr. apply Hs. eapply RReachTau; eauto. Qed.

  (** Safety survives every step of a visible event. *)
  Lemma rsafe_vis_inv {R X} (t : itree F R) (e : F X) k x Q h h' :
    observe t = VisF e k -> rstep h e x h' -> rsafe t Q h -> rsafe (k x) Q h'.
  Proof. intros Ho Hst Hs h'' u Hr. apply Hs. eapply RReachVis; eauto. Qed.

  (** Sequencing: [t] is safe and lands where [k] is safe.  Every proof
      walks a program with this rule, one [bind] at a time. *)
  Lemma rsafe_bind {T U} (t : itree F T) (k : T -> itree F U) Q h :
    rsafe t (fun r h1 => rsafe (k r) Q h1) h -> rsafe (ITree.bind t k) Q h.
  Proof.
    intros Hs h' u Hr.
    destruct (rreach_bind _ _ _ _ _ Hr) as [(t1 & H1 & ->) | (t1 & r & h1 & H1 & H2 & H3)].
    - pose proof (Hs _ _ H1) as Ho. unfold rok in *. rewrite observe_bind.
      destruct (observe t1) as [r|t2|X e k1]; auto.
      exact (rsafe_ok _ _ _ Ho).
    - pose proof (Hs _ _ H1) as Ho. unfold rok in Ho. rewrite H2 in Ho. exact (Ho _ _ H3).
  Qed.

  (** Sequencing through an intermediate postcondition [P], so that a spec
      proved for a callee can be reused at each call. *)
  Lemma rsafe_seq {T U} (t : itree F T) (k : T -> itree F U) P Q h :
    rsafe t P h -> (forall r h1, P r h1 -> rsafe (k r) Q h1) -> rsafe (ITree.bind t k) Q h.
  Proof.
    intros Ht Hk. apply rsafe_bind. intros h' u Hr. specialize (Ht h' u Hr).
    unfold rok in *. destruct (observe u); auto.
  Qed.

  (** [Ret x] is safe when [x] already satisfies the postcondition. *)
  Lemma rsafe_ret {R} (x : R) (Q : R -> S -> Prop) h : Q x h -> rsafe (Ret x) Q h.
  Proof. intros HQ h' u Hr. inversion Hr; subst; cbn in *; try discriminate. exact HQ. Qed.

  (** Weakening the postcondition. *)
  Lemma rsafe_conseq {R} (t : itree F R) (Q Q' : R -> S -> Prop) h :
    rsafe t Q h -> (forall r h', Q r h' -> Q' r h') -> rsafe t Q' h.
  Proof.
    intros Hs HQ h' u Hr. specialize (Hs h' u Hr). unfold rok in *.
    destruct (observe u); auto.
  Qed.

  (** A silent step in front keeps a tree safe. *)
  Lemma rsafe_tau {R} (t : itree F R) Q h : rsafe t Q h -> rsafe (Tau t) Q h.
  Proof.
    intros Hs h' u Hr. inversion Hr as [| ? ? t' ? ? Ho Hr' | ? ? ? ? ? ? ? ? ? Ho]; subst.
    - exact I.
    - cbn in Ho. injection Ho as <-. exact (Hs _ _ Hr').
    - discriminate.
  Qed.

  (** A visible event is safe if it is allowed or has a step, and the
      continuation is safe after each of its steps. *)
  Lemma rsafe_vis {R X} (e : F X) (k : X -> itree F R) Q h :
    (allow e \/ exists x h', rstep h e x h') ->
    (forall x h', rstep h e x h' -> rsafe (k x) Q h') ->
    rsafe (Vis e k) Q h.
  Proof.
    intros Hex Hk h' u Hr. inversion Hr as [| ? ? ? ? ? Ho | ? ? Y e' k' x h1 ? ? Ho Hst Hr']; subst.
    - exact Hex.
    - discriminate.
    - cbn in Ho. injection Ho as -> He Hk'. apply inj_pair2 in He, Hk'. subst.
      exact (Hk _ _ Hst _ _ Hr').
  Qed.

  (** A single event, answered: safe if it is allowed or has a step, and
      each of its steps satisfies [Q]. *)
  Lemma rsafe_trigger {X} (e : F X) (Q : X -> S -> Prop) h :
    (allow e \/ exists x h', rstep h e x h') ->
    (forall x h', rstep h e x h' -> Q x h') ->
    rsafe (ITree.trigger e) Q h.
  Proof. intros Hex HQ. apply rsafe_vis; auto. intros x h' Hst. apply rsafe_ret, HQ, Hst. Qed.

  (** An allowed event with no step is safe whatever follows. *)
  Lemma rsafe_allowed {R X} (e : F X) (k : X -> itree F R) Q h :
    allow e -> (forall x h', ~ rstep h e x h') -> rsafe (Vis e k) Q h.
  Proof. intros Ha Hn. apply rsafe_vis; [left; exact Ha | intros x h' Hst; destruct (Hn _ _ Hst)]. Qed.

  (** Strongly bisimilar trees reach bisimilar configurations. *)
  Lemma rreach_eq_itree {R} h (t' : itree F R) h' u' :
    rreach h t' h' u' -> forall t, t ≅ t' -> exists u, rreach h t h' u /\ u ≅ u'.
  Proof.
    induction 1 as [h t' | h t' t1' h' u' Ho Hr IH | h t' X e k' x h1 h' u' Ho Hst Hr IH];
      intros t Ht.
    - exists t. split; [constructor | exact Ht].
    - pose proof (itree_eta t') as Et. rewrite Ho in Et.
      destruct (eqitree_inv_Tau_r t t1' (transitivity Ht Et)) as (t1 & Ho1 & Ht1).
      destruct (IH t1 Ht1) as (u & Hu & Heq). exists u. split; [eapply RReachTau; eauto | exact Heq].
    - pose proof (itree_eta t') as Et. rewrite Ho in Et.
      destruct (eqitree_inv_Vis_r t e k' (transitivity Ht Et)) as (k1 & Ho1 & Hk1).
      destruct (IH (k1 x) (Hk1 x)) as (u & Hu & Heq). exists u. split; [eapply RReachVis; eauto | exact Heq].
  Qed.

  (** Being not stuck is invariant under strong bisimulation. *)
  Lemma rok_eq_itree {R} (Q : R -> S -> Prop) h (t t' : itree F R) :
    t ≅ t' -> rok Q h t -> rok Q h t'.
  Proof.
    intros Ht Hok. pose proof (itree_eta t') as Et. unfold rok in *.
    destruct (observe t') as [r|t1'|X e k'] eqn:Ho; auto.
    - rewrite (eqitree_inv_Ret_r t r (transitivity Ht Et)) in Hok. exact Hok.
    - destruct (eqitree_inv_Vis_r t e k' (transitivity Ht Et)) as (k1 & Ho1 & _).
      rewrite Ho1 in Hok. exact Hok.
  Qed.

  (** Safety is invariant under strong bisimulation, so a tree may be
      rewritten with the [eq_itree] laws before it is walked. *)
  Lemma rsafe_eq_itree {R} (t t' : itree F R) Q h :
    t ≅ t' -> rsafe t Q h -> rsafe t' Q h.
  Proof.
    intros Ht Hs h' u' Hr. destruct (rreach_eq_itree _ _ _ _ Hr t Ht) as (u & Hu & Heq).
    exact (rok_eq_itree _ _ _ _ Heq (Hs _ _ Hu)).
  Qed.

End Rel.

(** * Interpreting one layer of [Global] events

    A tree over [Global.Event T V +' F] has a layered semantics over some
    state [Hp] that splits as the [Global] store and a state [S] for the
    rest ([join]): [Global] events act on the store as [hstep] says, the
    other events as a semantics of [F] says, and no [Global] event may be
    performed without a step.  Then [Global.interp] of a safe tree is safe
    under the semantics of [F], its answer's store joined back in. *)
Section Layer.

  Context {T : Type} (ltu : T -> T -> Prop) `{Ix T ltu} {EQD : EqDec T eq}.
  Context `{Global.RefClass T} {V : T -> Type}.
  Context {M : Type} `{HMap (@idx_key T T) (idx_key_type V) M}.
  Context `{Foldable M (sigT (@idx_key_type T T V))}.
  Context {F : Type -> Type} `{exceptE Err -< F}.
  Context {S Hp : Type}.
  Context (stepF : forall {X : Type}, S -> F X -> X -> S -> Prop).
  Context (allowF : forall {X : Type}, F X -> Prop).
  Context (stepG : forall {X : Type}, Hp -> (Global.Event T V +' F) X -> X -> Hp -> Prop).
  Context (allowG : forall {X : Type}, (Global.Event T V +' F) X -> Prop).
  Context (join : M -> S -> Hp).
  Arguments stepF {X}. Arguments allowF {X}. Arguments stepG {X}. Arguments allowG {X}.

  (** A [Global] event with a step is one [hstep] answers. *)
  Hypothesis layer_inl_step : forall X (e : Global.Event T V X) m s x h',
    stepG (join m s) (inl1 e) x h' -> hstep ltu e m <> None.
  (** [hstep]'s answer is a step. *)
  Hypothesis layer_inl_hstep : forall X (e : Global.Event T V X) m s m' x,
    hstep ltu e m = Some (m', x) -> stepG (join m s) (inl1 e) x (join m' s).
  (** No [Global] event is a sanctioned exit. *)
  Hypothesis layer_inl_allow : forall X (e : Global.Event T V X), ~ allowG (inl1 e).
  (** Another event with a step has a step of [F]. *)
  Hypothesis layer_inr_step : forall X (f : F X) m s x h',
    stepG (join m s) (inr1 f) x h' -> exists s', stepF s f x s'.
  (** A step of [F] is a step that leaves the store alone. *)
  Hypothesis layer_inr_stepF : forall X (f : F X) m s x s',
    stepF s f x s' -> stepG (join m s) (inr1 f) x (join m s').
  (** The sanctioned exits among the other events are those of [F]. *)
  Hypothesis layer_inr_allow : forall X (f : F X), allowG (inr1 f) -> allowF f.

  (** [Global.interp] only looks at the head of the tree. *)
  Lemma interp_observe {R} (t t' : itree (Global.Event T V +' F) R) (m : M) :
    observe t = observe t' -> Global.interp ltu R t m ≅ Global.interp ltu R t' m.
  Proof.
    intros Ho. rewrite (interp_unfold_any ltu t), (interp_unfold_any ltu t'), Ho.
    reflexivity.
  Qed.

  (** The head of a tree bisimilar to the interpretation of a safe tree:
      an answer, a silent step to the interpretation of another safe tree,
      or an event of [F] passed through. *)
  Lemma layer_cases {R} (t0 : itree (Global.Event T V +' F) R) m0 s Q w :
    rsafe (@stepG) (@allowG) t0 Q (join m0 s) -> w ≅ Global.interp ltu R t0 m0 ->
    (exists r, observe t0 = RetF r /\ observe w = RetF (m0, r)) \/
    (exists t1 m1 w1, observe w = TauF w1 /\ w1 ≅ Global.interp ltu R t1 m1 /\
                      rsafe (@stepG) (@allowG) t1 Q (join m1 s)) \/
    (exists X (f : F X) k k0, observe t0 = VisF (inr1 f) k /\ observe w = VisF f k0 /\
                              forall x, k0 x ≅ Tau (Global.interp ltu R (k x) m0)).
  Proof.
    intros Hs Hw.
    assert (Hi : Global.interp ltu R t0 m0 ≅ Global.interp ltu R (go (observe t0)) m0)
      by (apply interp_observe; reflexivity).
    destruct (observe t0) as [r|t1|X [e|f] k] eqn:Ho.
    - left. exists r. split; [reflexivity|]. apply eqitree_inv_Ret_r.
      rewrite Hw, Hi. apply interp_ret_any.
    - right; left.
      destruct (eqitree_inv_Tau_r w (Global.interp ltu R t1 m0)) as (w1 & Hwo & Hw1).
      { rewrite Hw, Hi. apply interp_tau_any. }
      exists t1, m0, w1. split; [exact Hwo | split; [exact Hw1 |]].
      eapply rsafe_tau_inv; eauto.
    - right; left.
      pose proof (rsafe_ok _ _ _ _ _ Hs) as Hok. unfold rok in Hok. rewrite Ho in Hok.
      destruct Hok as [Ha | (x & h' & Hst)]; [destruct (layer_inl_allow _ _ Ha)|].
      destruct (hstep ltu e m0) as [[m1 x1]|] eqn:Hh;
        [| destruct (layer_inl_step _ _ _ _ _ _ Hst Hh)].
      destruct (eqitree_inv_Tau_r w (Global.interp ltu R (k x1) m1)) as (w1 & Hwo & Hw1).
      { rewrite Hw, Hi. apply interp_vis_inl, Hh. }
      exists (k x1), m1, w1. split; [exact Hwo | split; [exact Hw1 |]].
      eapply rsafe_vis_inv; [exact Ho | apply layer_inl_hstep, Hh | exact Hs].
    - right; right.
      destruct (eqitree_inv_Vis_r w f (fun x => Tau (Global.interp ltu R (k x) m0)))
        as (k0 & Hwo & Hk0).
      { rewrite Hw, Hi. apply interp_vis_inr. }
      exists X, f, k, k0. auto.
  Qed.

  (** Every configuration the interpretation reaches is not stuck. *)
  Lemma layer_reach {R} (Q : R -> Hp -> Prop) s s' w u :
    rreach (@stepF) s w s' u ->
    forall t0 m0, rsafe (@stepG) (@allowG) t0 Q (join m0 s) ->
    w ≅ Global.interp ltu R t0 m0 ->
    rok (@stepF) (@allowF) (fun p s1 => Q (snd p) (join (fst p) s1)) s' u.
  Proof.
    induction 1 as [s w | s w w' s' u Ho Hr IH | s w X e k' x s1 s' u Ho Hst Hr IH];
      intros t0 m0 Hs Hw;
      destruct (layer_cases t0 m0 s Q w Hs Hw)
        as [(r & Ht & Hwo) | [(t1 & m1 & w1 & Hwo & Hw1 & Hs1) | (Y & f & k & k0 & Ht & Hwo & Hk)]];
      try (rewrite Hwo in Ho; discriminate).
    - pose proof (rsafe_ok _ _ _ _ _ Hs) as Hok. unfold rok in *. rewrite Ht in Hok.
      rewrite Hwo. exact Hok.
    - unfold rok. rewrite Hwo. exact I.
    - pose proof (rsafe_ok _ _ _ _ _ Hs) as Hok. unfold rok in *. rewrite Ht in Hok.
      rewrite Hwo. destruct Hok as [Ha | (x & h' & Hst)].
      + left. apply layer_inr_allow, Ha.
      + right. destruct (layer_inr_step _ _ _ _ _ _ Hst) as (s' & Hs'). eauto.
    - rewrite Hwo in Ho. injection Ho as <-. exact (IH t1 m1 Hs1 Hw1).
    - rewrite Hwo in Ho. injection Ho as -> He Hk'. apply inj_pair2 in He, Hk'. subst.
      apply (IH (Tau (k x)) m0).
      + apply rsafe_tau. eapply rsafe_vis_inv; [exact Ht | apply layer_inr_stepF, Hst | exact Hs].
      + rewrite Hk. symmetry. apply interp_tau_any.
  Qed.

  (** Interpreting the [Global] events of a safe tree gives a safe tree. *)
  Theorem rsafe_interp {R} (t : itree (Global.Event T V +' F) R) (Q : R -> Hp -> Prop) m s :
    rsafe (@stepG) (@allowG) t Q (join m s) ->
    rsafe (@stepF) (@allowF) (Global.interp ltu R t m)
      (fun p s1 => Q (snd p) (join (fst p) s1)) s.
  Proof. intros Hs s' u Hr. eapply layer_reach; [exact Hr | exact Hs | reflexivity]. Qed.

End Layer.

(** * The solver's heap and events *)

(** The store [Global.run] uses for cells typed by [V]. *)
Notation store V := (halist (@idx_key nat nat) (@idx_key_type nat nat V)).
(** The store of [nat] cells. *)
Notation Mn := (store Solver.Vn).
(** The store of array cells. *)
Notation Ma := (store Solver.Va).
(** A heap: both stores. *)
Definition heap : Type := (Mn * Ma)%type.

(** The exception the solver is allowed to raise: [Solver.out_of_fuel]'s. *)
Definition is_out_of_fuel {X} (e : exceptE Err X) : Prop :=
  match e with Throw err => err = Error "out of fuel"%pstring end.

(** The events left once the [Vn] events are interpreted. *)
Notation Ea := (Global.Event nat Solver.Va +' exceptE Err).

(** A [Va] event steps as [hstep] says; an exception has no step. *)
Definition step_a {X} (m : Ma) (e : Ea X) (x : X) (m' : Ma) : Prop :=
  match e with
  | inl1 e => hstep Nat.le e m = Some (m', x)
  | inr1 _ => False
  end.

(** The sanctioned exit among the [Ea] events. *)
Definition allow_a {X} (e : Ea X) : Prop :=
  match e with
  | inl1 _ => False
  | inr1 f => is_out_of_fuel f
  end.

(** One event against the heap: a [Vn] event acts on the first store, the
    rest act as [step_a] on the second. *)
Definition step {X} (h : heap) (e : Solver.E X) (x : X) (h' : heap) : Prop :=
  match e with
  | inl1 e => hstep Nat.le e (fst h) = Some (fst h', x) /\ snd h' = snd h
  | inr1 f => fst h' = fst h /\ step_a (snd h) f x (snd h')
  end.

(** The sanctioned exit: throwing "out of fuel". *)
Definition allow {X} (e : Solver.E X) : Prop :=
  match e with
  | inl1 _ => False
  | inr1 f => allow_a f
  end.

(** [reach h t h' u]: [t], started in [h], gets to [u] in [h']. *)
Definition reach {R} : heap -> itree Solver.E R -> heap -> itree Solver.E R -> Prop :=
  rreach (@step).

(** A configuration that is not stuck: a [Vis] one is OK iff it is the
    program's own "out of fuel" exception or has a step. *)
Definition ok_at {R} (Q : R -> heap -> Prop) (h : heap) (t : itree Solver.E R) : Prop :=
  rok (@step) (@allow) Q h t.

(** Every configuration [t] reaches from [h] is not stuck, and a finished
    one satisfies [Q]. *)
Definition safe {R} (t : itree Solver.E R) (Q : R -> heap -> Prop) (h : heap) : Prop :=
  forall h' u, reach h t h' u -> ok_at Q h' u.

(** * Structural rules *)

(** Sequencing: [t] is safe and lands where [k] is safe. *)
Lemma safe_bind {T U} (t : itree Solver.E T) (k : T -> itree Solver.E U) Q h :
  safe t (fun r h1 => safe (k r) Q h1) h -> safe (ITree.bind t k) Q h.
Proof. apply rsafe_bind. Qed.

(** Sequencing through an intermediate postcondition [P]. *)
Lemma safe_seq {T U} (t : itree Solver.E T) (k : T -> itree Solver.E U) P Q h :
  safe t P h -> (forall r h1, P r h1 -> safe (k r) Q h1) -> safe (ITree.bind t k) Q h.
Proof. apply rsafe_seq. Qed.

(** [Ret x] is safe when [x] already satisfies the postcondition. *)
Lemma safe_ret {R} (x : R) (Q : R -> heap -> Prop) h : Q x h -> safe (Ret x) Q h.
Proof. apply rsafe_ret. Qed.

(** Weakening the postcondition. *)
Lemma safe_conseq {R} (t : itree Solver.E R) (Q Q' : R -> heap -> Prop) h :
  safe t Q h -> (forall r h', Q r h' -> Q' r h') -> safe t Q' h.
Proof. apply rsafe_conseq. Qed.

(** A silent step in front keeps a tree safe. *)
Lemma safe_tau {R} (t : itree Solver.E R) Q h : safe t Q h -> safe (Tau t) Q h.
Proof. apply rsafe_tau. Qed.

(** Safety is invariant under strong bisimulation. *)
Lemma safe_eq_itree {R} (t t' : itree Solver.E R) Q h :
  t ≅ t' -> safe t Q h -> safe t' Q h.
Proof. apply rsafe_eq_itree. Qed.

(** Running out of fuel is safe whatever the postcondition: it is the
    sanctioned way out of a loop. *)
Lemma safe_out_of_fuel (Q : nat -> heap -> Prop) h : safe Solver.out_of_fuel Q h.
Proof.
  unfold Solver.out_of_fuel, failwith, throw.
  apply rsafe_allowed; [reflexivity | intros [] ].
Qed.

(** [safe_out_of_fuel] followed by anything. *)
Lemma safe_out_of_fuel_bind {U} (k : nat -> itree Solver.E U) Q h :
  safe (ITree.bind Solver.out_of_fuel k) Q h.
Proof. apply safe_bind, safe_out_of_fuel. Qed.

(** A [Vn] event, answered: safe if [hstep] answers on the first store, and
    each answer satisfies [Q]. *)
Lemma safe_trigger_n {X} (e : Global.Event nat Solver.Vn X) (Q : X -> heap -> Prop) mn ma :
  (exists x m', hstep Nat.le e (mn) = Some (m', x)) ->
  (forall x m', hstep Nat.le e (mn) = Some (m', x) -> Q x (m', ma)) ->
  safe (ITree.trigger (inl1 e)) Q (mn, ma).
Proof.
  intros (x & m' & Hs) HQ. apply rsafe_trigger.
  - right. exists x, (m', ma). cbn. auto.
  - intros y [m1 m2] [Hy Hm]. cbn in *. subst. apply HQ, Hy.
Qed.

(** A [Va] event, answered: safe if [hstep] answers on the second store,
    and each answer satisfies [Q]. *)
Lemma safe_trigger_a {X} (e : Global.Event nat Solver.Va X) (Q : X -> heap -> Prop) mn ma :
  (exists x m', hstep Nat.le e (ma) = Some (m', x)) ->
  (forall x m', hstep Nat.le e (ma) = Some (m', x) -> Q x (mn, m')) ->
  safe (ITree.trigger (inr1 (inl1 e))) Q (mn, ma).
Proof.
  intros (x & m' & Hs) HQ. apply rsafe_trigger.
  - right. exists x, (mn, m'). cbn. auto.
  - intros y [m1 m2] [Hm Hy]. cbn in *. subst. apply HQ, Hy.
Qed.

(** * Arrays and references in a store *)

(** The location of an array's element [0]. *)
Definition abase {A} (a : Global.array nat A) : nat := let '(MkArray b _) := a in b.
(** The number of elements of an array. *)
Definition asize {A} (a : Global.array nat A) : nat := let '(MkArray _ n) := a in n.
(** The locations of an array's elements, in order. *)
Definition cells {A} (a : Global.array nat A) : list nat := seq (abase a) (asize a).

Section Store.

  (** The type of the cells, at index [0], of the store in question. *)
  Context {V : nat -> Type}.

  (** Array [a] holds [xs] in [m]: [xs] has [a]'s size, and cell
      [abase a + i] holds element [i]. *)
  Definition arr (m : store V) (a : Global.array nat (V 0)) (xs : list (V 0)) : Prop :=
    length xs = asize a /\
    forall i, i < asize a -> lookup (abase a + i, 0) m = nth_error xs i.

  (** Reference [r] holds [v] in [m]. *)
  Definition refp (m : store V) (r : @Global.ref nat _ (V 0)) (v : V 0) : Prop :=
    lookup (Global.ref_index (V 0) r, 0) m = Some v.

  (** [m] after writing [x] to element [i] of [a]. *)
  Definition awrite (m : store V) (a : Global.array nat (V 0)) (i : nat) (x : V 0) : store V :=
    add (Global.shift Nat.le (abase a) i, 0) x m.

  (** The array [new_array] makes in [m]: [n] elements from [fresh m]. *)
  Definition afresh (m : store V) (n : nat) : Global.array nat (V 0) :=
    MkArray (Global.fresh Nat.le m) n.

  (** [m] after [new_array] of [n] copies of [x]. *)
  Definition anew (m : store V) (n : nat) (x : V 0) : store V :=
    Global.fill (V := V) Nat.le 0 x (Global.fresh Nat.le m) n m.

  (** The reference [new_ref] makes in [m]: at [fresh m]. *)
  Definition rfresh (m : store V) : @Global.ref nat _ (V 0) :=
    Global.make_ref (V 0) (Global.fresh Nat.le m).

  (** [m] after [new_ref] of [v]. *)
  Definition rnew (m : store V) (v : V 0) : store V := add (Global.fresh Nat.le m, 0) v m.

  (** [m] after writing [v] to [r]. *)
  Definition rwrite (m : store V) (r : @Global.ref nat _ (V 0)) (v : V 0) : store V :=
    add (Global.ref_index (V 0) r, 0) v m.

  (** A location is a cell of [a] exactly when it lies in [a]'s range. *)
  Lemma in_cells {A} (a : Global.array nat A) l : In l (cells a) <-> abase a <= l < abase a + asize a.
  Proof. apply in_seq. Qed.

  (** The size of an array is the length of its contents. *)
  Lemma arr_length m a xs : arr m a xs -> length xs = asize a.
  Proof. now intros [Hl _]. Qed.

  (** Element [i] of the contents is the store's cell [abase a + i]. *)
  Lemma arr_lookup m a xs i x :
    arr m a xs -> nth_error xs i = Some x -> lookup (abase a + i, 0) m = Some x.
  Proof.
    intros [Hl Hc] Hx. rewrite Hc; [exact Hx|]. rewrite <- Hl. apply nth_error_Some. congruence.
  Qed.

  (** An array holds one list. *)
  Lemma arr_inj m a xs ys : arr m a xs -> arr m a ys -> xs = ys.
  Proof.
    intros [Hl Hc] [Hl' Hc']. apply nth_error_ext. intros i.
    destruct (Nat.lt_ge_cases i (asize a)) as [Hi|Hi].
    - rewrite <- Hc, <- Hc'; auto.
    - rewrite (proj2 (nth_error_None xs i)), (proj2 (nth_error_None ys i)); auto; lia.
  Qed.

  (** A reference holds one value. *)
  Lemma refp_inj m r v w : refp m r v -> refp m r w -> v = w.
  Proof. unfold refp. congruence. Qed.

  (** Every cell of an array the store holds lies below [fresh]. *)
  Lemma arr_cells_lt_fresh m a xs l :
    arr m a xs -> In l (cells a) -> l < Global.fresh Nat.le m.
  Proof.
    intros Ha Hl. apply in_cells in Hl.
    destruct (nth_error xs (l - abase a)) as [x|] eqn:Hx.
    - pose proof (arr_lookup _ _ _ _ _ Ha Hx) as Hk.
      replace (abase a + (l - abase a)) with l in Hk by lia.
      exact (lookup_lt_fresh _ _ _ Hk).
    - apply nth_error_None in Hx. rewrite (arr_length _ _ _ Ha) in Hx. lia.
  Qed.

  (** A reference the store holds lies below [fresh]. *)
  Lemma refp_lt_fresh m r v : refp m r v -> Global.ref_index (V 0) r < Global.fresh Nat.le m.
  Proof. intros Hr. exact (lookup_lt_fresh _ _ _ Hr). Qed.

  (** The written element now holds [x]. *)
  Lemma arr_awrite_same m a i x xs :
    arr m a xs -> i < length xs -> arr (awrite m a i x) a (lset xs i x).
  Proof.
    intros [Hl Hc] Hi. split; [now rewrite lset_length|]. intros j Hj.
    unfold awrite. rewrite shift_nat. destruct (Nat.eq_dec j i) as [->|Hne].
    - rewrite lookup_add_eq, nth_error_lset_eq; auto.
    - rewrite lookup_add_neq by (intros Hk; injection Hk; lia).
      rewrite nth_error_lset_neq by lia. auto.
  Qed.

  (** A write leaves every other cell alone. *)
  Lemma lookup_awrite_other m a i x l j :
    (l, j) <> (abase a + i, 0) -> lookup (l, j) (awrite m a i x) = lookup (l, j) m.
  Proof. intros Hk. unfold awrite. rewrite shift_nat. apply lookup_add_neq. auto. Qed.

  (** A write leaves an array not holding the written cell alone. *)
  Lemma arr_awrite_other m a i x b ys :
    arr m b ys -> ~ In (abase a + i) (cells b) -> arr (awrite m a i x) b ys.
  Proof.
    intros [Hl Hc] Hn. split; [exact Hl|]. intros j Hj.
    rewrite lookup_awrite_other; auto. intros Hk. injection Hk as Hk.
    apply Hn, in_cells. lia.
  Qed.

  (** A write leaves a reference at another location alone. *)
  Lemma refp_awrite m a i x r v :
    refp m r v -> Global.ref_index (V 0) r <> abase a + i -> refp (awrite m a i x) r v.
  Proof.
    unfold refp. intros Hr Hn. rewrite lookup_awrite_other; auto. intros Hk. injection Hk. auto.
  Qed.

  (** The new array has size [n]. *)
  Lemma asize_afresh m n : asize (afresh m n) = n.
  Proof. reflexivity. Qed.

  (** The new array starts at [fresh]. *)
  Lemma abase_afresh m n : abase (afresh m n) = Global.fresh Nat.le m.
  Proof. reflexivity. Qed.

  (** The new array holds [n] copies of [x]. *)
  Lemma arr_anew m n x : arr (anew m n x) (afresh m n) (repeat x n).
  Proof.
    split; [apply repeat_length|]. intros i Hi. cbn [abase asize afresh] in *.
    unfold anew. rewrite lookup_fill_in by lia. now rewrite nth_error_repeat.
  Qed.

  (** Outside the new array's cells the store is unchanged. *)
  Lemma lookup_anew_out m n x l j :
    ~ In l (cells (afresh m n)) -> lookup (l, j) (anew m n x) = lookup (l, j) m.
  Proof.
    intros Hn. unfold anew. apply lookup_fill_out. intros [Hl _]. apply Hn, in_cells. exact Hl.
  Qed.

  (** The new array's cells were unbound. *)
  Lemma afresh_unbound m n l j : In l (cells (afresh m n)) -> lookup (l, j) m = None.
  Proof. intros Hl. apply in_cells in Hl. apply lookup_fresh_none. cbn [abase asize afresh] in Hl. lia. Qed.

  (** The new array shares no cell with an array the store holds. *)
  Lemma afresh_disjoint m n b ys l :
    arr m b ys -> In l (cells b) -> ~ In l (cells (afresh m n)).
  Proof.
    intros Hb Hl Hn. pose proof (arr_cells_lt_fresh _ _ _ _ Hb Hl).
    apply in_cells in Hn. cbn [abase asize afresh] in Hn. lia.
  Qed.

  (** [new_array] leaves every array the store holds alone. *)
  Lemma arr_anew_old m n x b ys : arr m b ys -> arr (anew m n x) b ys.
  Proof.
    intros Hb. split; [exact (arr_length _ _ _ Hb)|]. intros i Hi.
    rewrite lookup_anew_out; [apply (proj2 Hb), Hi|].
    apply (afresh_disjoint _ _ _ _ _ Hb), in_cells. lia.
  Qed.

  (** [new_array] leaves every reference the store holds alone. *)
  Lemma refp_anew m n x r v : refp m r v -> refp (anew m n x) r v.
  Proof.
    intros Hr. pose proof (refp_lt_fresh _ _ _ Hr). unfold refp.
    rewrite lookup_anew_out; [exact Hr|]. intros Hn. apply in_cells in Hn. cbn [abase asize afresh] in Hn. lia.
  Qed.

  (** The reference just written holds [v]. *)
  Lemma refp_rwrite_same m r v : refp (rwrite m r v) r v.
  Proof. exact (lookup_add_eq _ _ _). Qed.

  (** Writing [r] leaves every other location alone. *)
  Lemma lookup_rwrite_other m r v l j :
    (l, j) <> (Global.ref_index (V 0) r, 0) -> lookup (l, j) (rwrite m r v) = lookup (l, j) m.
  Proof. intros Hk. apply lookup_add_neq. auto. Qed.

  (** Writing [r] leaves a reference at another location alone. *)
  Lemma refp_rwrite_other m r v r' w :
    Global.ref_index (V 0) r' <> Global.ref_index (V 0) r -> refp m r' w -> refp (rwrite m r v) r' w.
  Proof.
    unfold refp. intros Hn Hr. rewrite lookup_rwrite_other; auto. intros Hk. injection Hk. auto.
  Qed.

  (** Writing [r] leaves an array not holding [r]'s location alone. *)
  Lemma arr_rwrite m r v a xs :
    arr m a xs -> ~ In (Global.ref_index (V 0) r) (cells a) -> arr (rwrite m r v) a xs.
  Proof.
    intros [Hl Hc] Hn. split; [exact Hl|]. intros i Hi.
    rewrite lookup_rwrite_other; auto. intros Hk. apply (f_equal fst) in Hk. cbn [fst] in Hk.
    apply Hn, in_cells. rewrite <- Hk. lia.
  Qed.

  (** The new reference holds [v]. *)
  Lemma refp_rnew m v : refp (rnew m v) (rfresh m) v.
  Proof. exact (lookup_add_eq _ _ _). Qed.

  (** The new reference's location was unbound. *)
  Lemma rfresh_unbound m j : lookup (Global.ref_index (V 0) (rfresh m), j) m = None.
  Proof. apply lookup_fresh_none. reflexivity. Qed.

  (** [new_ref] leaves every location below [fresh] alone. *)
  Lemma lookup_rnew_old m v l j :
    l < Global.fresh Nat.le m -> lookup (l, j) (rnew m v) = lookup (l, j) m.
  Proof. intros Hl. apply lookup_add_neq. intros Hk. apply (f_equal fst) in Hk. cbn [fst] in Hk. lia. Qed.

  (** [new_ref] leaves every array the store holds alone. *)
  Lemma arr_rnew m v a xs : arr m a xs -> arr (rnew m v) a xs.
  Proof.
    intros Ha. split; [exact (arr_length _ _ _ Ha)|]. intros i Hi.
    rewrite lookup_rnew_old; [apply (proj2 Ha), Hi|].
    apply (arr_cells_lt_fresh _ _ _ _ Ha), in_cells. lia.
  Qed.

  (** [new_ref] leaves every reference the store holds alone. *)
  Lemma refp_rnew_old m v r w : refp m r w -> refp (rnew m v) r w.
  Proof.
    intros Hr. unfold refp. rewrite lookup_rnew_old; [exact Hr|]. exact (refp_lt_fresh _ _ _ Hr).
  Qed.

End Store.

(** * One rule per operation

    Each rule demands what makes the event step (a live array and an index
    in bounds, a live reference) and continues with the answer and the
    heap the step leaves.  The [_bind] forms step over one statement of a
    sequence.  [nat] arrays live in the first store, the array of arrays
    and the reference in the second.  Heaps are written as explicit pairs
    [(mn, ma)]: a rule over a heap variable [h] would leave
    [(anew (fst h) n x, snd h)], and a sequence of such steps duplicates
    [h] at every step, so unification time doubles per statement. *)

(** Element [i] of a [nat] array. *)
Lemma safe_read_n (a : Solver.narr) i xs x (Q : nat -> heap -> Prop) mn ma :
  arr (mn) a xs -> nth_error xs i = Some x -> Q x (mn, ma) ->
  safe (Global.read_array (E := Solver.E) (V := Solver.Vn) (idx := 0) a i) Q (mn, ma).
Proof.
  intros Ha Hx HQ. pose proof (arr_lookup _ _ _ _ _ Ha Hx) as Hk.
  pose proof (arr_length _ _ _ Ha) as Hl. assert (Hi : i < length xs) by (apply nth_error_Some; congruence).
  destruct a as [b n]. cbn [abase asize] in Hk, Hl. rewrite Hl in Hi. rewrite <- shift_nat in Hk.
  apply (safe_trigger_n (ReadArray nat Solver.Vn 0 (MkArray b n) i)); cbn [hstep];
    rewrite (proj2 (Nat.ltb_lt i n) Hi), Hk.
  - eexists _, _. reflexivity.
  - intros y m' Hs. injection Hs as <- <-. exact HQ.
Qed.

(** [safe_read_n] in front of the rest of a sequence. *)
Lemma safe_read_n_bind {U} (a : Solver.narr) i xs x (k : nat -> itree Solver.E U) Q mn ma :
  arr (mn) a xs -> nth_error xs i = Some x -> safe (k x) Q (mn, ma) ->
  safe (ITree.bind (Global.read_array (E := Solver.E) (V := Solver.Vn) (idx := 0) a i) k) Q (mn, ma).
Proof. intros Ha Hx Hk. apply safe_bind. exact (safe_read_n a i xs x _ mn ma Ha Hx Hk). Qed.

(** Write element [i] of a [nat] array. *)
Lemma safe_write_n (a : Solver.narr) i (x : nat) xs (Q : unit -> heap -> Prop) mn ma :
  arr (mn) a xs -> i < length xs -> Q tt (awrite (mn) a i x, ma) ->
  safe (Global.write_array (E := Solver.E) (V := Solver.Vn) (idx := 0) a i x) Q (mn, ma).
Proof.
  intros Ha Hi HQ. rewrite (arr_length _ _ _ Ha) in Hi. destruct a as [b n]. cbn [asize] in Hi.
  apply (safe_trigger_n (WriteArray nat Solver.Vn 0 (MkArray b n) i x)); cbn [hstep];
    rewrite (proj2 (Nat.ltb_lt i n) Hi).
  - eexists _, _. reflexivity.
  - intros [] m' Hs. injection Hs as <-. exact HQ.
Qed.

(** [safe_write_n] in front of the rest of a sequence. *)
Lemma safe_write_n_bind {U} (a : Solver.narr) i (x : nat) xs (k : unit -> itree Solver.E U) Q mn ma :
  arr (mn) a xs -> i < length xs -> safe (k tt) Q (awrite (mn) a i x, ma) ->
  safe (ITree.bind (Global.write_array (E := Solver.E) (V := Solver.Vn) (idx := 0) a i x) k) Q (mn, ma).
Proof. intros Ha Hi Hk. apply safe_bind. exact (safe_write_n a i x xs _ mn ma Ha Hi Hk). Qed.

(** A new [nat] array: [afresh], in the store [anew]. *)
Lemma safe_new_n n (x : nat) (Q : Solver.narr -> heap -> Prop) mn ma :
  Q (afresh (mn) n) (anew (mn) n x, ma) ->
  safe (Global.new_array (E := Solver.E) (V := Solver.Vn) 0 n x) Q (mn, ma).
Proof.
  intros HQ. apply (safe_trigger_n (NewArray nat Solver.Vn 0 n x)); cbn [hstep].
  - eexists _, _. reflexivity.
  - intros a m' Hs. injection Hs as <- <-. exact HQ.
Qed.

(** [safe_new_n] in front of the rest of a sequence. *)
Lemma safe_new_n_bind {U} n (x : nat) (k : Solver.narr -> itree Solver.E U) Q mn ma :
  safe (k (afresh (mn) n)) Q (anew (mn) n x, ma) ->
  safe (ITree.bind (Global.new_array (E := Solver.E) (V := Solver.Vn) 0 n x) k) Q (mn, ma).
Proof. intros Hk. apply safe_bind. exact (safe_new_n n x _ mn ma Hk). Qed.

(** Exchange elements [i] and [j] of a [nat] array. *)
Lemma safe_swap_n (a : Solver.narr) i j xi xj xs (Q : unit -> heap -> Prop) mn ma :
  arr (mn) a xs -> nth_error xs i = Some xi -> nth_error xs j = Some xj ->
  Q tt (awrite (awrite (mn) a i xj) a j xi, ma) ->
  safe (Global.swap_array (E := Solver.E) (V := Solver.Vn) (idx := 0) a i j) Q (mn, ma).
Proof.
  intros Ha Hi Hj HQ. unfold Global.swap_array.
  assert (Hil : i < length xs) by (apply nth_error_Some; congruence).
  assert (Hjl : j < length xs) by (apply nth_error_Some; congruence).
  apply (safe_read_n_bind a i xs xi); auto.
  apply (safe_read_n_bind a j xs xj); auto.
  apply (safe_write_n_bind a i xj xs); auto.
  apply (safe_write_n a j xi (lset xs i xj)); cbn [fst snd].
  - apply (arr_awrite_same (V := Solver.Vn)); auto.
  - now rewrite lset_length.
  - exact HQ.
Qed.

(** [safe_swap_n] in front of the rest of a sequence. *)
Lemma safe_swap_n_bind {U} (a : Solver.narr) i j xi xj xs (k : unit -> itree Solver.E U) Q mn ma :
  arr (mn) a xs -> nth_error xs i = Some xi -> nth_error xs j = Some xj ->
  safe (k tt) Q (awrite (awrite (mn) a i xj) a j xi, ma) ->
  safe (ITree.bind (Global.swap_array (E := Solver.E) (V := Solver.Vn) (idx := 0) a i j) k) Q (mn, ma).
Proof. intros Ha Hi Hj Hk. apply safe_bind. exact (safe_swap_n a i j xi xj xs _ mn ma Ha Hi Hj Hk). Qed.

(** Element [i] of the array of arrays. *)
Lemma safe_read_a (a : Global.array nat Solver.narr) i xs x (Q : Solver.narr -> heap -> Prop) mn ma :
  arr (ma) a xs -> nth_error xs i = Some x -> Q x (mn, ma) ->
  safe (Global.read_array (E := Solver.E) (V := Solver.Va) (idx := 0) a i) Q (mn, ma).
Proof.
  intros Ha Hx HQ. pose proof (arr_lookup _ _ _ _ _ Ha Hx) as Hk.
  pose proof (arr_length _ _ _ Ha) as Hl. assert (Hi : i < length xs) by (apply nth_error_Some; congruence).
  destruct a as [b n]. cbn [abase asize] in Hk, Hl. rewrite Hl in Hi. rewrite <- shift_nat in Hk.
  apply (safe_trigger_a (ReadArray nat Solver.Va 0 (MkArray b n) i)); cbn [hstep];
    rewrite (proj2 (Nat.ltb_lt i n) Hi), Hk.
  - eexists _, _. reflexivity.
  - intros y m' Hs. injection Hs as <- <-. exact HQ.
Qed.

(** [safe_read_a] in front of the rest of a sequence. *)
Lemma safe_read_a_bind {U} (a : Global.array nat Solver.narr) i xs x
    (k : Solver.narr -> itree Solver.E U) Q mn ma :
  arr (ma) a xs -> nth_error xs i = Some x -> safe (k x) Q (mn, ma) ->
  safe (ITree.bind (Global.read_array (E := Solver.E) (V := Solver.Va) (idx := 0) a i) k) Q (mn, ma).
Proof. intros Ha Hx Hk. apply safe_bind. exact (safe_read_a a i xs x _ mn ma Ha Hx Hk). Qed.

(** Write element [i] of the array of arrays. *)
Lemma safe_write_a (a : Global.array nat Solver.narr) i (x : Solver.narr) xs
    (Q : unit -> heap -> Prop) mn ma :
  arr (ma) a xs -> i < length xs -> Q tt (mn, awrite (ma) a i x) ->
  safe (Global.write_array (E := Solver.E) (V := Solver.Va) (idx := 0) a i x) Q (mn, ma).
Proof.
  intros Ha Hi HQ. assert (Hi' : i < asize a) by (rewrite <- (arr_length _ _ _ Ha); exact Hi).
  clear Hi. destruct a as [b n]. cbn [asize] in Hi'.
  apply (safe_trigger_a (WriteArray nat Solver.Va 0 (MkArray b n) i x)); cbn [hstep];
    rewrite (proj2 (Nat.ltb_lt i n) Hi').
  - eexists _, _. reflexivity.
  - intros [] m' Hs. injection Hs as <-. exact HQ.
Qed.

(** [safe_write_a] in front of the rest of a sequence. *)
Lemma safe_write_a_bind {U} (a : Global.array nat Solver.narr) i (x : Solver.narr) xs
    (k : unit -> itree Solver.E U) Q mn ma :
  arr (ma) a xs -> i < length xs -> safe (k tt) Q (mn, awrite (ma) a i x) ->
  safe (ITree.bind (Global.write_array (E := Solver.E) (V := Solver.Va) (idx := 0) a i x) k) Q (mn, ma).
Proof. intros Ha Hi Hk. apply safe_bind. exact (safe_write_a a i x xs _ mn ma Ha Hi Hk). Qed.

(** A new array of arrays: [afresh], in the store [anew]. *)
Lemma safe_new_a n (x : Solver.narr) (Q : Global.array nat Solver.narr -> heap -> Prop) mn ma :
  Q (afresh (ma) n) (mn, anew (ma) n x) ->
  safe (Global.new_array (E := Solver.E) (V := Solver.Va) 0 n x) Q (mn, ma).
Proof.
  intros HQ. apply (safe_trigger_a (NewArray nat Solver.Va 0 n x)); cbn [hstep].
  - eexists _, _. reflexivity.
  - intros a m' Hs. injection Hs as <- <-. exact HQ.
Qed.

(** [safe_new_a] in front of the rest of a sequence. *)
Lemma safe_new_a_bind {U} n (x : Solver.narr) (k : Global.array nat Solver.narr -> itree Solver.E U) Q mn ma :
  safe (k (afresh (ma) n)) Q (mn, anew (ma) n x) ->
  safe (ITree.bind (Global.new_array (E := Solver.E) (V := Solver.Va) 0 n x) k) Q (mn, ma).
Proof. intros Hk. apply safe_bind. exact (safe_new_a n x _ mn ma Hk). Qed.

(** A new reference to an array: [rfresh], in the store [rnew]. *)
Lemma safe_new_ref (v : Solver.narr) (Q : @Global.ref nat _ Solver.narr -> heap -> Prop) mn ma :
  Q (rfresh (ma)) (mn, rnew (ma) v) ->
  safe (Global.new_ref (E := Solver.E) (V := Solver.Va) 0 v) Q (mn, ma).
Proof.
  intros HQ. apply (safe_trigger_a (NewRef nat Solver.Va 0 v)); cbn [hstep].
  - eexists _, _. reflexivity.
  - intros r m' Hs. injection Hs as <- <-. exact HQ.
Qed.

(** [safe_new_ref] in front of the rest of a sequence. *)
Lemma safe_new_ref_bind {U} (v : Solver.narr) (k : @Global.ref nat _ Solver.narr -> itree Solver.E U) Q mn ma :
  safe (k (rfresh (ma))) Q (mn, rnew (ma) v) ->
  safe (ITree.bind (Global.new_ref (E := Solver.E) (V := Solver.Va) 0 v) k) Q (mn, ma).
Proof. intros Hk. apply safe_bind. exact (safe_new_ref v _ mn ma Hk). Qed.

(** Read a live reference. *)
Lemma safe_read_ref (r : @Global.ref nat _ Solver.narr) v (Q : Solver.narr -> heap -> Prop) mn ma :
  refp (ma) r v -> Q v (mn, ma) ->
  safe (Global.read_ref (E := Solver.E) (V := Solver.Va) (idx := 0) r) Q (mn, ma).
Proof.
  intros Hr HQ. apply (safe_trigger_a (ReadRef nat Solver.Va 0 r)); cbn [hstep];
    unfold refp in Hr; rewrite Hr.
  - eexists _, _. reflexivity.
  - intros y m' Hs. injection Hs as <- <-. exact HQ.
Qed.

(** [safe_read_ref] in front of the rest of a sequence. *)
Lemma safe_read_ref_bind {U} (r : @Global.ref nat _ Solver.narr) v
    (k : Solver.narr -> itree Solver.E U) Q mn ma :
  refp (ma) r v -> safe (k v) Q (mn, ma) ->
  safe (ITree.bind (Global.read_ref (E := Solver.E) (V := Solver.Va) (idx := 0) r) k) Q (mn, ma).
Proof. intros Hr Hk. apply safe_bind. exact (safe_read_ref r v _ mn ma Hr Hk). Qed.

(** Write a reference. *)
Lemma safe_write_ref (r : @Global.ref nat _ Solver.narr) (v : Solver.narr) (Q : unit -> heap -> Prop) mn ma :
  Q tt (mn, rwrite (ma) r v) ->
  safe (Global.write_ref (E := Solver.E) (V := Solver.Va) (idx := 0) r v) Q (mn, ma).
Proof.
  intros HQ. apply (safe_trigger_a (WriteRef nat Solver.Va 0 r v)); cbn [hstep].
  - eexists _, _. reflexivity.
  - intros [] m' Hs. injection Hs as <-. exact HQ.
Qed.

(** [safe_write_ref] in front of the rest of a sequence. *)
Lemma safe_write_ref_bind {U} (r : @Global.ref nat _ Solver.narr) (v : Solver.narr)
    (k : unit -> itree Solver.E U) Q mn ma :
  safe (k tt) Q (mn, rwrite (ma) r v) ->
  safe (ITree.bind (Global.write_ref (E := Solver.E) (V := Solver.Va) (idx := 0) r v) k) Q (mn, ma).
Proof. intros Hk. apply safe_bind. exact (safe_write_ref r v _ mn ma Hk). Qed.

(** * The bridge to [Global]'s model *)

(** [taus t u]: [t] gets to [u] by finitely many silent steps. *)
Inductive taus {F R} : itree F R -> itree F R -> Prop :=
| TausRefl t : taus t t
| TausTau t t' u : observe t = TauF t' -> taus t' u -> taus t u.

(** A run of the model that never goes wrong: every configuration it
    reaches by silent steps is silent, an answer satisfying [P], or the
    "out of fuel" exception. *)
Definition model_safe {R} (P : R -> Prop) (t : itree (exceptE Err) R) : Prop :=
  forall u, taus t u ->
  match observe u with
  | RetF r => P r
  | TauF _ => True
  | VisF e _ => is_out_of_fuel e
  end.

(** No step for exceptions. *)
Definition step_e {X} (_ : unit) (_ : exceptE Err X) (_ : X) (_ : unit) : Prop := False.

(** Under [step_e], safety is [model_safe]. *)
Lemma rsafe_model_safe {R} (t : itree (exceptE Err) R) (P : R -> Prop) :
  rsafe (@step_e) (@is_out_of_fuel) t (fun r _ => P r) tt -> model_safe P t.
Proof.
  intros Hs u Hu. assert (Hr : rreach (@step_e) tt t tt u).
  { clear Hs. induction Hu as [t0 | t0 t1 u0 Ho _ IH]; [apply RReachRefl | eapply RReachTau; [exact Ho | exact IH]]. }
  specialize (Hs _ _ Hr). unfold rok in Hs.
  destruct (observe u); auto. destruct Hs as [Ha | (x & h & [])]. exact Ha.
Qed.

(** A safe tree's two-layer run under [Global]'s model, from stores [mn]
    and [ma], fails only with "out of fuel", and its answers satisfy [Q]
    on the final stores. *)
Theorem safe_model {R} (t : itree Solver.E R) (Q : R -> heap -> Prop) (mn : Mn) (ma : Ma) :
  safe t Q (mn, ma) ->
  model_safe (fun '(ma', (mn', r)) => Q r (mn', ma'))
    (Global.interp Nat.le _ (Global.interp Nat.le R t mn) ma).
Proof.
  intros Hs.
  assert (H1 : rsafe (@step_a) (@allow_a) (Global.interp Nat.le R t mn)
                 (fun p s1 => Q (snd p) (fst p, s1)) ma).
  { apply (rsafe_interp Nat.le (@step_a) (@allow_a) (@step) (@allow) pair);
      [| | intros X e Ha; exact Ha | | | intros X f Ha; exact Ha | exact Hs].
    - intros X e m s x h' [Hh _] Hn. cbn [fst] in Hh. rewrite Hn in Hh. discriminate.
    - intros X e m s m' x Hh. split; [exact Hh | reflexivity].
    - intros X f m s x h' [_ Hst]. eauto.
    - intros X f m s x s' Hst. split; [reflexivity | exact Hst]. }
  assert (H2 := rsafe_interp Nat.le (@step_e) (@is_out_of_fuel) (@step_a) (@allow_a)
                  (fun m _ => m) ltac:(intros X e m s x h' Hh Hn; unfold step_a in Hh; rewrite Hn in Hh; discriminate)
                  ltac:(intros X e m s m' x Hh; exact Hh)
                  ltac:(intros X e Ha; exact Ha)
                  ltac:(intros X f m s x h' [])
                  ltac:(intros X f m s x s' [])
                  ltac:(intros X f Ha; exact Ha)
                  (Global.interp Nat.le R t mn) _ ma tt H1).
  apply rsafe_model_safe. eapply rsafe_conseq; [exact H2|].
  intros [ma' [mn' r]] []. cbn. auto.
Qed.

(** [safe_model] from the empty stores, as [Global.run] runs. *)
Corollary safe_run {R} (t : itree Solver.E R) (Q : R -> heap -> Prop) :
  safe t Q ([], []) ->
  model_safe (fun '(ma', (mn', r)) => Q r (mn', ma')) (Global.run (Global.run t)).
Proof. apply safe_model. Qed.
