From Stdlib Require Import Nat.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyDecltype.

(** When loopify converts a list fold whose per-element contribution
    is an if-then-else (not a plain variable), the generated [_Call1]
    struct uses [decltype([&]() -> unsigned int { ... }())] to declare
    the field type.  This is invalid C++:
      - [&] capture-default has no enclosing scope in a struct definition
      - [_args] is not in scope at the struct definition site

    A simple [unsigned int] (or the appropriate concrete type) should
    be used instead. *)

(** Minimal trigger: fold over a list with a conditional per-element
    contribution. *)
Fixpoint count_true (xs : list bool) : nat :=
  match xs with
  | [] => 0
  | b :: rest => (if b then 1 else 0) + count_true rest
  end.

(** Same pattern with a record field access inside the conditional. *)
Record item : Type := mkItem { item_flag : bool; item_val : nat }.

Fixpoint sum_flagged (xs : list item) : nat :=
  match xs with
  | [] => 0
  | x :: rest =>
    (if item_flag x then item_val x else 0) + sum_flagged rest
  end.

End LoopifyDecltype.

Set Crane Loopify.
Crane Extraction "loopify_decltype" LoopifyDecltype.
