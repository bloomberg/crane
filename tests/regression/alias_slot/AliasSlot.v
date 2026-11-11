(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** [Set Crane SharedVariant]: a type alias of a shared variant
    ([Definition parts := list string]) is held as the variant is. *)
From Stdlib Require Import List String.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Local Open Scope string_scope.

Module AliasSlot.

Definition parts := list string.

Inductive expr : Type :=
| ELit (s : string)
| EAdd (a b : expr).

Fixpoint expr_parts (e : expr) (k : parts) : parts :=
  match e with
  | ELit s => s :: k
  | EAdd a b =>
      let rest := "+" :: expr_parts b k in
      match a with
      | EAdd _ _ => "(" :: expr_parts a (")" :: rest)
      | ELit _ => expr_parts a rest
      end
  end.

(** Each of [xs] with a comma after it, then [k]: a loop that fills the
    tail of the cell before, a cell whose type is the alias. *)
Fixpoint comma_parts (xs : list string) (k : parts) : parts :=
  match xs with
  | [] => k
  | x :: r => x :: "," :: comma_parts r k
  end.

Record line : Type := mkLine { l_indent : nat; l_text : parts }.

Definition line_of (e : expr) : line := mkLine 2 (expr_parts e []).

Definition count (e : expr) : nat := List.length (l_text (line_of e)).

Definition sample : nat := count (EAdd (EAdd (ELit "a") (ELit "b")) (ELit "c")).

Definition commas : nat := List.length (comma_parts ["a"; "b"; "c"] ["end"]).

End AliasSlot.

Set Crane Loopify.
Set Crane SharedVariant.
Crane Extraction "alias_slot" AliasSlot.
