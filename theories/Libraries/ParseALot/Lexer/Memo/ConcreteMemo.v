(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import FSets FSets.FMapAVL FSets.FMapFacts.

From Crane.Libraries.ParseALot.Lexer Require Import State.
From Crane.Libraries.ParseALot.Lexer.Memo Require Import Memo.
From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Utils Require Import Orders.
(** Toggle point for benchmarking: comment/uncomment exactly one of these two
    imports. Both [NativeMap] (extracted to [immer::map] / an OCaml AVL
    [Map]) and [NativeMapBaseline] (a plain association list, no custom
    binding) define a module named [NativeMap] with an identical interface,
    so nothing below this line needs to change either way. *)
From Crane.Libraries.ParseALot.Utils Require Import NativeMap.
(* From Crane.Libraries.ParseALot.Utils Require Import NativeMapBaseline. *)
From Crane Require Import Extraction.


(** Concrete AVL-map–backed memo table satisfying the [Memo] interface.

    Each pointer maps to a [NativeMap] (extracted to [immer::map]) keyed directly
    on the position [index], replacing the former hand-rolled binary trie keyed on
    the bit-serialized position. *)
Module FMemo (STT : State.T) <: Memo STT.

  Import STT.Ty.
  Import STT.Defs.
  Import STT.R.Defs.

  (** Ordered type wrapper for [Pointer] used as AVL map keys. *)
  Module Pointer_as_UOT <: UsualOrderedType := UOT_from_UCT Pointer_as_UCT.
  (** AVL finite map keyed by [Pointer]. *)
  Module FM := FMapAVL.Make Pointer_as_UOT.
  (** Facts and lemmas for [FM]. *)
  Module FMF := FMapFacts.Facts FM.
  (* Bisecting global-arena hang: the lexer's per-pointer memo table,
     persistent AVL map growing via path-copying over the whole lex. See
     project_crane_arena_ambient memory. *)
  Crane NoArena FM.Raw.tree.

  (** A memo table maps each pointer to an [index]-keyed map of cached results. *)
  Definition Memo : Type :=
    FM.t (NativeMap.t index (option (String * String * index))).
  (** The empty memo table containing no cached entries. *)
  Definition emptyMemo : Memo :=
    FM.empty (NativeMap.t index (option (String * String * index))).

  (** Look up the cached result for [(pnt, i)] in memo [M], returning [None] if absent. *)
  Definition get_Memo (M : Memo) (pnt : Pointer) (i : index)
    : option (option (String * String * index)) :=
    match FM.find pnt M with
    | None => None
    | Some T => NativeMap.get T i
    end.

  (** Store result [o] for key [(pnt, i)] into memo [M]. *)
  Definition set_Memo (M : Memo) (pnt : Pointer) (i : index)
             (o : (option (String * String * index))) : Memo :=
    match FM.find pnt M with
    | None => FM.add pnt (NativeMap.set NativeMap.empty i o) M
    | Some T => FM.add pnt (NativeMap.set T i o) M
    end.

  (** Reading back the just-written key always returns [Some o]; by [NativeMap.get_set]. *)
  Lemma correct_Memo : forall M ptr i o, get_Memo (set_Memo M ptr i o) ptr i = Some o.
  Proof.
    intros. unfold get_Memo. unfold set_Memo. repeat dm.
    - rewrite FMF.add_eq_o in E; auto. repeat inj_all. apply NativeMap.get_set.
    - rewrite FMF.add_eq_o in E; auto. repeat inj_all. apply NativeMap.get_set.
    - rewrite FMF.add_eq_o in E; auto. discriminate.
    - rewrite FMF.add_eq_o in E; auto. discriminate.
  Qed.


  (** Writing to a different key [(ptr', i')] does not affect lookup at [(ptr, i)];
      by [NativeMap.get_set_moot]. *)
  Lemma correct_Memo_moot : forall M ptr ptr' i i' o,
      (ptr <> ptr' \/ i <> i')
      ->
      get_Memo (set_Memo M ptr' i' o) ptr i = get_Memo M ptr i.
  Proof.
    intros M ptr ptr' i i' o H.
    unfold get_Memo, set_Memo.
    destruct (Pointer_as_UOT.eq_dec ptr ptr') as [Ep | Ep].
    - (* Same pointer: the disjunction forces [i <> i']. *)
      subst ptr'.
      assert (Hi : i' <> i).
      { destruct H as [Hp | Hi]; [ contradiction | congruence ]. }
      destruct (FM.find ptr M) eqn:Ef.
      + rewrite FMF.add_eq_o by auto.
        rewrite NativeMap.get_set_moot by auto. reflexivity.
      + rewrite FMF.add_eq_o by auto.
        rewrite NativeMap.get_set_moot by auto.
        apply NativeMap.get_empty.
    - (* Distinct pointer: the write lands under a different key. *)
      destruct (FM.find ptr' M) eqn:Ef';
        rewrite FMF.add_neq_o by auto; reflexivity.
  Qed.

  (** The empty memo has no entries; follows from [FMapFacts.empty_o]. *)
  Lemma correct_emptyMemo : forall stt z, get_Memo emptyMemo stt z = None.
  Proof.
    intros. unfold get_Memo. unfold emptyMemo. repeat dm.
    rewrite FMF.empty_o in E. discriminate.
  Qed.


End FMemo.


(** Packages [FMemo] together with its definitions into the [Memo.T] interface. *)
Module memoTFn (STT' : State.T) <: Memo.T.
  Module STT := STT'.
  Module MemTy <: Memo STT := FMemo STT.
  Module Defs := Memo.MemoDefsFn STT MemTy.
End memoTFn.
