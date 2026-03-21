(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyTail.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

(** Tail-recursive: last element of a list *)
Fixpoint last {A : Type} (x : A) (l : list A) : A :=
  match l with
  | nil => x
  | cons y ls => last y ls
  end.

(** Tail-recursive: length with accumulator *)
Fixpoint length_acc {A : Type} (acc : nat) (l : list A) : nat :=
  match l with
  | nil => acc
  | cons _ ls => length_acc (S acc) ls
  end.

Definition length {A : Type} (l : list A) : nat :=
  length_acc O l.

(** Tail-recursive: membership test *)
Fixpoint member (x : nat) (l : list nat) : bool :=
  match l with
  | nil => false
  | cons y ys => if Nat.eqb x y then true else member x ys
  end.

(** Tail-recursive: nth element *)
Fixpoint nth (n : nat) (l : list nat) (default : nat) : nat :=
  match l with
  | nil => default
  | cons x xs => if Nat.eqb n O then x else nth (n - 1) xs default
  end.

(** Tail-recursive: fold_left *)
Fixpoint fold_left {A B : Type} (f : B -> A -> B) (acc : B) (l : list A) : B :=
  match l with
  | nil => acc
  | cons x xs => fold_left f (f acc x) xs
  end.

(** Tail-recursive: lookup in association list *)
Fixpoint lookup (key : nat) (l : list (nat * nat)) : nat :=
  match l with
  | nil => O
  | cons p rest =>
    if Nat.eqb (fst p) key then snd p else lookup key rest
  end.

End LoopifyTail.

Set Crane Loopify.
Crane Extraction "loopify_tail" LoopifyTail.
