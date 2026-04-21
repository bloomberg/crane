From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module FixEscapeMatch.

(** A local fixpoint inside a match branch capturing a pattern variable.
    The pattern variable h is a structured binding reference into the
    shared_ptr's data. The fixpoint captures it by [&], then escapes
    through an option constructor. After the match IIFE returns,
    h is destroyed — invoking the closure is use-after-free. *)
Definition make_fn_from_head (l : list nat) : option (nat -> nat) :=
  match l with
  | nil => None
  | cons h _ =>
    let fix add (x : nat) : nat :=
      match x with
      | O => h
      | S x' => S (add x')
      end
    in Some add
  end.

Definition test_match : nat :=
  match make_fn_from_head [10] with
  | Some f => f 3
  | None => 0
  end.

(** Variant: fixpoint captures TWO pattern variables from the match. *)
Definition make_fn_from_pair (l : list nat) : option (nat -> nat) :=
  match l with
  | cons a (cons b _) =>
    let fix combine (x : nat) : nat :=
      match x with
      | O => a + b
      | S x' => S (combine x')
      end
    in Some combine
  | _ => None
  end.

Definition test_match2 : nat :=
  match make_fn_from_pair [10; 20] with
  | Some f => f 3
  | None => 0
  end.

End FixEscapeMatch.

Crane Extraction "fix_escape_match" FixEscapeMatch.
