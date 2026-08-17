(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import List.
Import ListNotations.

From Stdlib Require Import ZArith.BinInt.

From Crane.Libraries.ParseALot.Lexer Require Import Regex.
From Crane.Libraries.ParseALot.Lexer Require Import State.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Abstraction.

From Crane.Libraries.ParseALot.Lexer.DFA Require Import Table.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import DFA.
From Crane.Libraries.ParseALot.Lexer.Lexer Require Import Impl.
From Crane.Libraries.ParseALot.Utils Require Import Ltac.
From Crane.Libraries.ParseALot.Utils Require Import AsciiFinite.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import ConcreteTable.

From Crane.Libraries.ParseALot.Lexer.Memo Require Import Memo.
From Crane.Libraries.ParseALot.Lexer.Memo Require Import Impl.
From Crane.Libraries.ParseALot.Lexer.Memo Require Import Correctness.
From Crane.Libraries.ParseALot.Lexer.Memo Require Import ConcreteMemo.
From Crane.Libraries.ParseALot.Lexer.Memo Require Import IntLexer.

(** Instantiates the full memoized lexer for a concrete alphabet and label set. *)
Module LexerFn (A : Sigma) (L : Label).

  (** Concrete [Memo.T] instance built from the DFA-based state and [FMemo]. *)
  Module Export Mem <: Memo.T.

    (** Concrete [State.T] built on top of the DFA table for [A]. *)
    Module Export STT <: State.T.

      (** Concrete [Table.T] parameterized by the regex type over [A]. *)
      Module TabT <: Table.T.

        (** Concrete [Regex.T] using [A] as the character type. *)
        Module Export R <: Regex.T.

          (** Character type for regexes, directly the [A] module. *)
          Module Export Ty <: Sigma := A.

          (** Regex definitions (combinators, matching, derivatives). *)
          Module Export Defs := Regex.DefsFn Ty.

        End R.

        (** Concrete finite-map–backed DFA transition table. *)
        Module TabTy <: Table R := FTable R.

        (** Table definitions (filling, canonicalization). *)
        Module Export Defs := DefsFn R TabTy.

      End TabT.

      Module Export R := TabT.R.
      Import R.Ty.
      Export R.Defs.Helpers.

      (** Integer-interned state type: swaps the regex-keyed DFA [Ty] for
          [IntLexer]'s [N]-indexed interned DFA (see [Lexer.Memo.IntLexer] and
          [Lexer.DFA.IntDFA]); everything downstream ([STT], [FMemo],
          [CorrectFn], [LitLexer], [SemLexerFn], ...) is generic in [State.T]
          and needs no change. *)
      Module Export Ty <: State R := IntLexer.TyFn TabT L.

      (** State definitions (pointer comparison, string operations) derived from [R] and [Ty]. *)
      Module Export Defs := State.DefsFn R Ty.

    End STT.

    (** Concrete AVL-backed memo table satisfying the [Memo] interface. *)
    Module Export MemTy <: Memo STT := FMemo STT.

    (** Memo invariant definitions derived from the concrete state and memo types. *)
    Module Export Defs := Memo.MemoDefsFn STT MemTy.

  End Mem.

  (** Correctness theorems (soundness and completeness) for the memoized lexer. *)
  Module Import Correctness := Memo.Correctness.CorrectFn Mem.

  (** Lexer instance satisfying the abstract [Lexer] interface, using [lex_M]. *)
  Module Export LitLexer <: Lexer STT.

    Import Impl.
    Definition lex := lex_M.
    Definition lex_sound := lex_sound__M.
    Definition lex_complete := lex_complete__M.

  End LitLexer.

  Export STT.
  Export R.Defs.
  Export STT.Defs.
  Export STT.R.Defs.

End LexerFn.
