(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Lexer Require Import Regex.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import Table.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import DFA.
From Crane.Libraries.ParseALot.Utils Require Import Orders.
From Crane Require Import Extraction.

(** Concrete AVL-map implementation of the Table interface, keyed by (regex, Sigma) pairs. *)
Module FTable (R : Regex.T) <: Table R.

  Import R.
  Import R.Ty.
  Module DS := R.Defs.
  Module Sigma_as_UOT := R.Defs.T_as_UOT.
  Module regex_as_UOT := R.Defs.regex_as_UOT.
  Module pair_as_UOT := Pair_as_UOT regex_as_UOT Sigma_as_UOT.

  Module FM := FMapAVL.Make pair_as_UOT.
  Module FMF := FMapFacts.Facts FM.
  (* Bisecting global-arena hang: this is the DFA transition table itself,
     the central memoized structure of DFA construction -- persistent
     AVL map growing via path-copying, heavily aliased across incremental
     fills. See project_crane_arena_ambient memory. *)
  Crane NoArena FM.Raw.tree.
  Module reFS := R.Defs.reFS.


  (** A table is a pair of an AVL map from (regex, Sigma) to regex, and a set of known states. *)
  Definition Table : Type := (FM.t regex) * reFS.t.
  (** The empty table with no transitions and no states. *)
  Definition emptyTable : Table := (FM.empty regex, reFS.empty).

  (** Inserts or overwrites the transition from state [e] on symbol [a] to state [r]. *)
  Definition set_Table (T : Table) (e : regex) (a : Sigma) (r : regex) : Table :=
    match T with
    | (fm, fs) => (FM.add (e, a) r fm, fs)
    end.
  (** Looks up the transition from state [e] on symbol [a] in the map component of [T]. *)
  Definition get_Table (T : Table) (e : regex) (a : Sigma) : option regex :=
    FM.find (e, a) (fst T).

  (** [get_Table] immediately after [set_Table] returns the inserted value; proved by [FMF.add_eq_o]. *)
  Lemma correct_Table : forall T e a r, get_Table (set_Table T e a r) e a = Some (r).
  Proof.
    intros. unfold get_Table. unfold set_Table. destruct T.
    apply FMF.add_eq_o. auto.
  Qed.

  (** Setting entry [(e, b)] does not affect a different entry [(e0, a)]; proved by [FMF.add_neq_o]. *)
  Lemma moot_setTable : forall T e0 e a b r,
      a <> b
      \/ e <> e0
      -> get_Table (set_Table T e b r) e0 a = get_Table T e0 a.
  Proof.
    intros. unfold get_Table. unfold set_Table. destruct T.
    apply FMF.add_neq_o. destruct H; intros C; destruct H; injection C; intros; subst; auto.
  Qed.

  (** The empty map has no entries; proved by [FMF.empty_o]. *)
  Lemma correct_emptyTable : forall e a, get_Table emptyTable e a = None.
  Proof.
    intros. unfold get_Table. unfold emptyTable. simpl. apply FMF.empty_o.
  Qed.

  (** Inserts regex [e] into the state set of [T], leaving the transition map unchanged. *)
  Definition add_state (T : Table) (e : regex) : Table :=
    match T with
    | (fm, fs) => (fm, reFS.add e fs)
    end.

  (** Returns the set of states (second component) of a table. *)
  Definition get_states (T : Table) : reFS.t := snd T.

  (** The state set of [emptyTable] is the empty set. *)
  Lemma empty_states : get_states emptyTable = reFS.empty.
  Proof. auto. Qed.

  (** After [add_state T r], [r] is a member of [get_states]; proved by [reFS.add_1]. *)
  Lemma correct_states : forall T r, reFS.In r (get_states (add_state T r)).
  Proof.
    intros. unfold add_state. unfold get_states. destruct T. simpl. apply reFS.add_1. auto.
  Qed.

  (** [add_state] does not modify the transition map, so [get_Table] is unaffected. *)
  Lemma moot_add_state : forall T e a r,
      get_Table T e a = get_Table (add_state T r) e a.
  Proof.
    intros. unfold get_Table. unfold add_state. destruct T. simpl. auto.
  Qed.

  (** Returns [Some e] if [e] is already in the state set, otherwise [None]; used to detect known derivatives. *)
  Definition get_eq (T : Table) (e : regex) : option regex :=
    if reFS.mem e (snd T) then Some e else None.

  (** [get_eq T e = Some e'] implies [e'] is a state and [regex_eq e e' = true]; proved by membership and reflexivity. *)
  Lemma get_eq_correct : forall T e e',
      get_eq T e = Some e' -> reFS.In e' (get_states T) /\ regex_eq e e' = true.
  Proof.
    intros. unfold get_eq in H. destruct (reFS.mem e (snd T)) eqn:E; [|discriminate].
    injection H. intros. subst. split.
    - unfold get_states. apply reFS.mem_2. auto.
    - apply regex_eq_correct. auto.
  Qed.

  (** [add_state] inserts exactly one element into the state set. *)
  Lemma add_state_states : forall T r x,
      reFS.In x (get_states (add_state T r)) -> x = r \/ reFS.In x (get_states T).
  Proof.
    intros T r x H. unfold add_state, get_states in *. destruct T. simpl in *.
    destruct (R.Defs.regex_as_UOT.eq_dec x r) as [Heq|Hne]; [left; exact Heq|].
    right. apply reFS.add_3 with (x := r); auto.
  Qed.

  (** [add_state] never removes a state. *)
  Lemma add_state_mono : forall T r x,
      reFS.In x (get_states T) -> reFS.In x (get_states (add_state T r)).
  Proof.
    intros T r x H. unfold add_state, get_states in *. destruct T. simpl in *.
    apply reFS.add_2. auto.
  Qed.

  (** [set_Table] touches only the transition map, so the state set is unchanged. *)
  Lemma set_Table_states : forall T e a r,
      get_states (set_Table T e a r) = get_states T.
  Proof. intros. unfold set_Table, get_states. destruct T. auto. Qed.

  (** [get_eq] answers [None] only for regexes that are not yet states. *)
  Lemma get_eq_None : forall T e,
      get_eq T e = None -> ~ reFS.In e (get_states T).
  Proof.
    intros T e H. unfold get_eq in H. destruct (reFS.mem e (snd T)) eqn:E; [discriminate|].
    unfold get_states. intros C. apply reFS.mem_1 in C. rewrite C in E. discriminate.
  Qed.

  Module reFSP := FSetProperties.Properties reFS.

  (** Adding a genuinely new state increases the cardinality by exactly one. *)
  Lemma add_state_cardinal : forall T r,
      ~ reFS.In r (get_states T) ->
      reFS.cardinal (get_states (add_state T r)) = S (reFS.cardinal (get_states T)).
  Proof.
    intros T r H. unfold add_state, get_states in *. destruct T. simpl in *.
    apply reFSP.add_cardinal_2. auto.
  Qed.

End FTable.
