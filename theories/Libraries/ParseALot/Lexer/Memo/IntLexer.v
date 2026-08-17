(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import NArith.

From Crane.Libraries.ParseALot.Lexer Require Import Regex.
From Crane.Libraries.ParseALot.Lexer Require Import State.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import Table.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import DFA.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import IntDFA.
From Crane.Libraries.ParseALot.Utils Require Import Ltac.

(** Integer-interned [State.T] instance: same interface as [ConcreteLexer]'s
    DFA-based [Ty] (mirrored below), except [Pointer := N] (a DFA state id)
    instead of [Pointer := regex]. A transition is then a flat
    [matrix[id][code a]] array index (via [IntDFA.step]) instead of an
    AVL lookup keyed by structural regex comparison.

    Trust boundary: this is a *trusted realization*, in the same spirit as
    [Utils.NativeMap] -- the interned DFA is built by ordinary computable Coq
    code ([IntDFA.intern], reusing [regex2dfa] as its source of truth), but
    its two core correctness properties relating it back to the regex
    semantics ([accepts_matches], [accepting_dt_list]) used to be asserted as
    axioms here. They are now proved, from [IntDFA.int_accepts_correct]: the
    interned state list is saturated under the transition function at build
    time, so the closure the interning argument needs holds by construction
    rather than by assumption. *)
Module TyFn (TabT : Table.T) (L : Label) <: State TabT.R.

  Module Export D := IntDFAFn TabT.
  Import TabT.
  Import TabT.Defs.

  Definition Label : Type := L.Label.
  Definition defLabel : Label := L.defLabel.
  Lemma Label_eq_dec : forall (l l' : Label), {l = l'} + {l <> l'}.
  Proof. apply L.Label_eq_dec. Qed.

  (** Pointer into the interned DFA: a state id. *)
  Definition Pointer : Type := N.
  Definition defPointer : Pointer := 0%N.
  (** Delta: the interned transition matrix, the accept vector, and the
      original regex (kept verbatim so [init_state_inv] is trivial). *)
  Definition Delta : Type := (vec (vec N) * vec bool * regex).
  Definition defDelta : Delta := (vnil, vnil, EmptySet).
  Definition State := prod Pointer Delta.
  Definition defState := (defPointer, defDelta).

  (** Advances a state by one character: O(1) [matrix[id][code a]]. *)
  Definition transition (a : Sigma) (e : State) : State :=
    match e with
    | (id, (m, acc, r)) => (step m id a, (m, acc, r))
    end.

  (** Advances a state by a list of characters. *)
  Fixpoint transition_list (bs : list Sigma) (e : State) : State :=
    match bs with
    | [] => e
    | b :: bs' => transition_list bs' (transition b e)
    end.

  Lemma transition_list_nil : forall fsm,
      transition_list [] fsm = fsm.
  Proof. intros. reflexivity. Qed.

  Lemma transition_list_cons : forall bs a fsm,
      transition_list (a :: bs) fsm = transition_list bs (transition a fsm).
  Proof. intros. reflexivity. Qed.

  (** The delta component (matrix/accept/orig) is unchanged by a transition;
      only the state id changes. *)
  Lemma transition_Delta : forall a p p' d d',
      transition a (p, d) = (p', d') -> d = d'.
  Proof.
    intros a p p' d d' H. unfold transition in H. destruct d as [[m acc] r].
    inversion H. reflexivity.
  Qed.

  (** Whether the current state is accepting. *)
  Definition accepting (e : State) : bool :=
    match e with
    | (id, (_, acc, _)) => is_accepting acc id
    end.

  (** Whether string [s] is accepted starting from state [e]. *)
  Definition accepts (s : String) (e : State) : bool :=
    accepting (transition_list s e).

  Lemma accepts_nil : forall fsm, accepting fsm = accepts [] fsm.
  Proof. intros. reflexivity. Qed.

  Lemma accepts_transition : forall cand a fsm,
      accepts cand (transition a fsm) = accepts (a :: cand) fsm.
  Proof. intros. reflexivity. Qed.

  (** The initial interned state for regex [r]: intern it via [IntDFA], then
      keep [r] itself (unchanged) as part of [Delta]. *)
  Definition init_state (r : regex) : State := intern r.

  (** Recovering the original regex from a state is trivial: it was carried
      through [Delta] unchanged by [init_state]. *)
  Definition init_state_inv (e : State) : regex :=
    match e with
    | (_, (_, _, r)) => r
    end.

  (** [init_state_inv (init_state r) = r] literally (not just language
      equivalent), since the original regex is threaded through untouched. *)
  Lemma invert_init_correct : forall r s,
      exp_match s (init_state_inv (init_state r)) <-> exp_match s r.
  Proof. intros. unfold init_state_inv, init_state, intern. simpl. reflexivity. Qed.

  (** The interned run is exactly [IntDFA.run] on the state id, with the
      [Delta] carried along untouched. *)
  Lemma transition_list_run : forall bs id m acc r,
      transition_list bs (id, (m, acc, r)) = (run m id bs, (m, acc, r)).
  Proof.
    induction bs as [| b bs IH]; intros id m acc r; [reflexivity |].
    cbn [transition_list transition run]. apply IH.
  Qed.

  (** [accepts] on an interned initial state is [IntDFA.int_accepts]. *)
  Lemma accepts_int_accepts : forall s e,
      accepts s (init_state e) = int_accepts e s.
  Proof.
    intros s e. unfold accepts, init_state, int_accepts.
    destruct (intern e) as (sid & (m & acc) & r) eqn:E.
    rewrite transition_list_run. reflexivity.
  Qed.

  (** The interned DFA accepts exactly the strings matched by the regex it
      was built from. Formerly a trusted axiom; it is now [IntDFA]'s
      [int_accepts_correct], which holds unconditionally because [intern]
      runs on a state list that is saturated (hence provably closed) rather
      than merely checked. *)
  Theorem accepts_matches : forall (s : String) (e : regex),
      true = accepts s (init_state e) <-> exp_match s e.
  Proof.
    intros s e. rewrite accepts_int_accepts.
    split.
    - intros H. apply int_accepts_correct. auto.
    - intros H. symmetry. apply int_accepts_correct, H.
  Qed.

  (** Stepping the interned DFA through [bs] agrees with re-interning the
      Brzozowski derivative of [e] by [bs]: both decide [exp_match bs e], the
      former by [accepts_matches], the latter through
      [derivative_list_str]. Formerly a trusted axiom. *)
  Theorem accepting_dt_list : forall bs e,
      accepting (transition_list bs (init_state e))
      = accepting (init_state (derivative_list bs e)).
  Proof.
    intros bs e.
    assert (Hl : accepting (transition_list bs (init_state e))
                 = accepts bs (init_state e)) by reflexivity.
    assert (Hr : accepting (init_state (derivative_list bs e))
                 = accepts [] (init_state (derivative_list bs e)))
      by reflexivity.
    rewrite Hl, Hr, !accepts_int_accepts.
    destruct (int_accepts e bs) eqn:E1;
      destruct (int_accepts (derivative_list bs e) []) eqn:E2; auto.
    - exfalso. apply int_accepts_correct in E1.
      assert (int_accepts (derivative_list bs e) [] = true)
        by (apply int_accepts_correct, derivative_list_str, E1).
      congruence.
    - exfalso. apply int_accepts_correct in E2.
      rewrite derivative_list_str in E2.
      assert (int_accepts e bs = true) by (apply int_accepts_correct, E2).
      congruence.
  Qed.

  (** Pointers are compared as plain [N] values: O(1), no regex traversal. *)
  Definition pointer_compare (s1 s2 : Pointer) : comparison := N.compare s1 s2.

  Lemma pointer_compare_eq : forall x y,
      pointer_compare x y = Eq <-> x = y.
  Proof. intros. unfold pointer_compare. apply N.compare_eq_iff. Qed.

  Lemma pointer_compare_trans : forall c x y z,
      pointer_compare x y = c -> pointer_compare y z = c -> pointer_compare x z = c.
  Proof.
    intros c x y z H1 H2. unfold pointer_compare in *.
    destruct c.
    - apply N.compare_eq_iff in H1, H2. apply N.compare_eq_iff. congruence.
    - rewrite N.compare_lt_iff in *. exact (N.lt_trans _ _ _ H1 H2).
    - pose proof (N.compare_antisym x y) as Axy.
      pose proof (N.compare_antisym y z) as Ayz.
      rewrite H1 in Axy. rewrite H2 in Ayz. simpl in Axy, Ayz.
      rewrite N.compare_lt_iff in Axy, Ayz.
      pose proof (N.lt_trans _ _ _ Ayz Axy) as Axz.
      rewrite <- N.compare_lt_iff in Axz.
      rewrite (N.compare_antisym z x). rewrite Axz. reflexivity.
  Qed.

  (** Encodes a [positive] as a list of bits (LSB first) — copied verbatim
      from [ConcreteLexer]. *)
  Fixpoint pos2list (p : positive) : list bool :=
    match p with
    | xH => []
    | xO p' => false :: (pos2list p')
    | xI p' => true :: (pos2list p')
    end.

  Fixpoint list2pos (bs : list bool) : positive :=
    match bs with
    | [] => xH
    | false :: bs' => xO (list2pos bs')
    | true :: bs' => xI (list2pos bs')
    end.

  Lemma list_inv_pos : forall p,
      list2pos (pos2list p) = p.
  Proof.
    induction p; sis; try rewrite IHp; auto.
  Qed.

  Definition int2list (z : Z) : list bool :=
    match z with
    | 0%Z => []
    | Z.pos z' => true :: (pos2list z')
    | Z.neg z' => false :: (pos2list z')
    end.

  Definition list2int (bs : list bool) : Z :=
    match bs with
    | [] => 0%Z
    | true :: bs' => Z.pos (list2pos bs')
    | false :: bs' => Z.neg (list2pos bs')
    end.

  Lemma list_inv_int : forall z,
      list2int (int2list z) = z.
  Proof.
    destruct z.
    - sis. auto.
    - sis. rewrite list_inv_pos. auto.
    - sis. rewrite list_inv_pos. auto.
  Qed.

  Definition index : Type := Z.
  Definition index0 : index := 0%Z.

  Lemma index_eq_dec : forall (i ii : index), {i = ii} + {i <> ii}.
  Proof. repeat decide equality. Qed.

  Definition init_index (n : nat) : index :=
    match n with
    | 0 => index0
    | S m => Z.pos (P_of_succ_nat m)
    end.

  Definition index2list : index -> list bool := int2list.
  Definition list2index : list bool -> index := list2int.

  Lemma list_inv : forall (x : index), list2index (index2list x) = x.
  Proof. apply list_inv_int. Qed.

  Definition incr : index -> index := Z.succ.
  Definition decr : index -> index := Z.pred.

  Lemma decr_inv_incr : forall i, decr (incr i) = i.
  Proof. apply Z.pred_succ. Qed.

  Lemma incr_inv_decr : forall i, incr (decr i) = i.
  Proof. apply Z.succ_pred. Qed.

  Lemma decr_inv_S : forall n, decr (init_index (S n)) = init_index n.
  Proof.
    induction n; auto.
    sis. repeat dm.
    - sis. inv E0.
    - sis. inv E0. inv E. apply f_equal. rewrite H0. apply Pos.pred_double_succ.
    - sis. inv E0.
  Qed.

  Lemma incr_is_S : forall n, init_index (S n) = incr (init_index n).
  Proof.
    induction n; auto.
    unfold init_index. unfold incr. apply Pos2Z.inj_succ.
  Qed.

  Lemma n_det_index : forall n1 n2, init_index n1 = init_index n2 -> n1 = n2.
  Proof.
    intros. unfold init_index in *. destruct n1; destruct n2; try discriminate; auto.
    repeat rewrite Znat.Zpos_P_of_succ_nat in H. repeat rewrite <- Znat.Nat2Z.inj_succ in *.
    apply Znat.Nat2Z.inj; auto.
  Qed.

End TyFn.
