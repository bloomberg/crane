(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.


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


(** Concrete memo table satisfying the [Memo] interface.

    One [NativeMap] (extracted to [immer::map]) keyed by the pair of the
    pointer and the position [index]. A write is a single [NativeMap.set] on
    a map nothing else holds, so a backend can update it in place; the former
    two-level table (an AVL map from pointer to an [index]-keyed map) read the
    inner map out of an AVL node and re-added it, so the inner map was always
    shared at the write. *)
Module FMemo (STT : State.T) <: Memo STT.

  Import STT.Ty.
  Import STT.Defs.
  Import STT.R.Defs.

  (** A memo table maps each [(pointer, index)] pair to a cached result. *)
  Definition Memo : Type :=
    NativeMap.t (Pointer * index) (option (String * String * index)).
  (** The empty memo table containing no cached entries. *)
  Definition emptyMemo : Memo :=
    @NativeMap.empty (Pointer * index) (option (String * String * index)).

  (** Look up the cached result for [(pnt, i)] in memo [M], returning [None] if absent. *)
  Definition get_Memo (M : Memo) (pnt : Pointer) (i : index)
    : option (option (String * String * index)) :=
    NativeMap.get M (pnt, i).

  (** Store result [o] for key [(pnt, i)] into memo [M]. *)
  Definition set_Memo (M : Memo) (pnt : Pointer) (i : index)
             (o : (option (String * String * index))) : Memo :=
    NativeMap.set M (pnt, i) o.

  (** Reading back the just-written key always returns [Some o]; by [NativeMap.get_set]. *)
  Lemma correct_Memo : forall M ptr i o, get_Memo (set_Memo M ptr i o) ptr i = Some o.
  Proof.
    intros. unfold get_Memo, set_Memo. apply NativeMap.get_set.
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
    apply NativeMap.get_set_moot.
    intro E. inversion E. subst. destruct H; contradiction.
  Qed.

  (** The empty memo has no entries; by [NativeMap.get_empty]. *)
  Lemma correct_emptyMemo : forall stt z, get_Memo emptyMemo stt z = None.
  Proof.
    intros. unfold get_Memo, emptyMemo. apply NativeMap.get_empty.
  Qed.

End FMemo.


(** Packages [FMemo] together with its definitions into the [Memo.T] interface. *)
Module memoTFn (STT' : State.T) <: Memo.T.
  Module STT := STT'.
  Module MemTy <: Memo STT := FMemo STT.
  Module Defs := Memo.MemoDefsFn STT MemTy.
End memoTFn.
