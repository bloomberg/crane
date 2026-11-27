(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Large inductive type with 12+ constructors. *)

From Stdlib Require Import Nat Bool String List.
Import ListNotations.

Module LargeEnum.

(* === 12-constructor color enum === *)

Inductive color : Type :=
  | Red | Orange | Yellow | Green | Blue | Indigo | Violet
  | Black | White | Gray | Brown | Pink.

Definition color_to_nat (c : color) : nat :=
  match c with
  | Red => 0 | Orange => 1 | Yellow => 2 | Green => 3
  | Blue => 4 | Indigo => 5 | Violet => 6
  | Black => 7 | White => 8 | Gray => 9
  | Brown => 10 | Pink => 11
  end.

Definition is_warm (c : color) : bool :=
  match c with
  | Red | Orange | Yellow | Pink | Brown => true
  | _ => false
  end.

Definition is_neutral (c : color) : bool :=
  match c with
  | Black | White | Gray => true
  | _ => false
  end.

(* === Parameterized large inductive: AST with 10 node types === *)

Inductive tok : Type :=
  | TNum : nat -> tok
  | TPlus : tok
  | TMinus : tok
  | TStar : tok
  | TSlash : tok
  | TLParen : tok
  | TRParen : tok
  | TEq : tok
  | TBang : tok
  | TSemicolon : tok
  | TIdent : nat -> tok
  | TEOF : tok.

Definition tok_to_nat (t : tok) : nat :=
  match t with
  | TNum n => n
  | TPlus => 100
  | TMinus => 101
  | TStar => 102
  | TSlash => 103
  | TLParen => 104
  | TRParen => 105
  | TEq => 106
  | TBang => 107
  | TSemicolon => 108
  | TIdent n => 200 + n
  | TEOF => 999
  end.

Definition is_operator (t : tok) : bool :=
  match t with
  | TPlus | TMinus | TStar | TSlash => true
  | _ => false
  end.

(* === Test values === *)

Definition test_red : nat := color_to_nat Red.
Definition test_pink : nat := color_to_nat Pink.
Definition test_warm_red : bool := is_warm Red.
Definition test_warm_blue : bool := is_warm Blue.
Definition test_neutral_black : bool := is_neutral Black.
Definition test_neutral_red : bool := is_neutral Red.

Definition test_tok_num : nat := tok_to_nat (TNum 42).
Definition test_tok_plus : nat := tok_to_nat TPlus.
Definition test_tok_ident : nat := tok_to_nat (TIdent 3).
Definition test_tok_eof : nat := tok_to_nat TEOF.
Definition test_is_op_plus : bool := is_operator TPlus.
Definition test_is_op_num : bool := is_operator (TNum 0).

End LargeEnum.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "large_enum" LargeEnum.
