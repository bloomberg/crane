(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Crane.Libraries.ParseALot.Utils Require Import Ltac.

(** Binary trie data structure for mapping [list bool] keys to optional [A] values. *)
Module Trie.

  (** A binary trie node: either a leaf (empty) or a branch carrying an optional value and two subtries. *)
  Inductive trie {A : Type} : Type :=
  | Leaf
  | Branch (t : option A) (t0 t1 : trie).

  (** Insert or overwrite a [value] at [key] in trie [T], routing by each bit of the key. *)
  Fixpoint set_trie {A : Type} (T : trie) (key : list bool) (value : A) : trie :=
    match key with
    | [] =>
      match T with
      | Leaf => Branch (Some value) Leaf Leaf
      | Branch _ t0 t1 => Branch (Some value) t0 t1
      end
    | b :: bs =>
      match T with
      | Leaf =>
        if b then Branch None (set_trie Leaf bs value) Leaf
        else Branch None Leaf (set_trie Leaf bs value)
      | Branch t t0 t1 =>
        if b then Branch t (set_trie t0 bs value) t1
        else Branch t t0 (set_trie t1 bs value)
      end
    end.

  (** Look up the value associated with [key] in trie [T]; returns [None] if absent. *)
  Fixpoint get_trie {A : Type} (T : trie) (key : list bool) : option A :=
    match T with
    | Leaf => None
    | Branch t t0 t1 =>
      match key with
      | [] => t
      | b :: bs =>
        if b then get_trie t0 bs
        else get_trie t1 bs
      end
    end.

  (** Getting a key immediately after setting it returns the stored value; by induction on the key. *)
  Lemma get_set : forall {A : Type} key T (value : A),
      get_trie (set_trie T key value) key = Some value.
  Proof.
    induction key; intros.
    - sis. repeat dm.
    - sis. repeat dm; sis; apply IHkey.
  Qed.

  (** Setting key [k0] does not affect the value at a distinct key [k1]; by induction on [k0]. *)
  Lemma get_set_moot : forall {A : Type} k0 k1 (v : A) T,
      k0 <> k1
      -> get_trie (set_trie T k0 v) k1 = get_trie T k1.
  Proof.
    induction k0; destruct k1; intros.
    - contradiction.
    - clear H. sis. repeat dm. sis. repeat dm.
    - clear H. sis. repeat dm.
    - sis. repeat dm; sis; repeat dm; apply IHk0; intros C; destruct H; rewrite C; auto.
  Qed.

End Trie.
