(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Crane.Libraries.ParseALot.Lexer Require Import State.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Correct.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Impl.

(** Abstract interface for a memoization table keyed by pointer and index. *)
Module Type Memo (Import STT : State.T).

  Import STT.
  Import STT.Ty.

  Parameter Memo : Type.
  Parameter emptyMemo : Memo.
  Parameter set_Memo : Memo -> Pointer -> index -> option(String * String * index) -> Memo.
  Parameter get_Memo : Memo -> Pointer -> index -> option (option (String * String * index)).

  Parameter correct_Memo : forall M stt z o, get_Memo (set_Memo M stt z o) stt z = Some (o).
  Parameter correct_Memo_moot : forall M stt stt' z z' o,
      (stt <> stt' \/ z <> z')
      ->
      get_Memo (set_Memo M stt' z' o) stt z = get_Memo M stt z.
  Parameter correct_emptyMemo : forall stt z, get_Memo emptyMemo stt z = None.

End Memo.

(** Defines memo invariants and connects the memoized lexer to the naive lexer. *)
Module MemoDefsFn (STT : State.T) (MEM : Memo STT).

  Import MEM.
  Module Import NaiveLexer := Lexer.Impl.ImplFn STT.
  Module Import NaiveLexerF := Lexer.Correct.CorrectFn STT.
  Import STT.Ty.
  Import NaiveLexer.Lem.Impl.
  Import STT.R.Defs.Strings.

  (** Invariants relating memo table contents to the naive lexer. *)
  Module Invariants.

    (** [ith_suffix code sx i] holds when [sx] is the suffix of [code] at position [i]. *)
    Definition ith_suffix (code sx : String) (i : index) : Prop :=
      init_index (length sx) = i
      /\ exists px, px ++ sx = code.

    (** [lexy code M d] holds when every cached entry in [M] agrees with [max_pref_fn] under delta [d]. *)
    Definition lexy (code : String) (M : Memo) (d : Delta) : Prop :=
      forall stt z i o,
        (get_Memo M stt i = Some o
         -> ith_suffix code z i
         -> max_pref_fn z i (stt, d) = o)
    (*/\ (max_pref_fn z stt = o
         -> (get_Memo M stt z = Some o \/ get_Memo M stt z = None))*).

    (** [lexy_list code Ms] holds when every memo-delta pair in [Ms] satisfies [lexy]. *)
    Definition lexy_list (code : String) (Ms : list (Memo * Delta)) : Prop :=
      forall M d, In (M, d) Ms -> lexy code M d.

  End Invariants.


End MemoDefsFn.

(** Bundles [MemoDefsFn] as a module type for use as a functor parameter. *)
Module Type DefsT (STT : State.T) (Ty : Memo STT).
  Include MemoDefsFn STT Ty.
End DefsT.

(** Top-level module type combining a state type, a memo implementation, and its definitions. *)
Module Type T.
  Declare Module STT : State.T.
  Declare Module MemTy : Memo STT.
  Declare Module Defs : DefsT STT MemTy.
  Export STT.
  Export STT.Ty.
  Export MemTy.
End T.
