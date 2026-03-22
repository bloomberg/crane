(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyOption.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

(** [find_opt p l] returns the first element satisfying [p], or None. *)
Fixpoint find_opt {A : Type} (p : A -> bool) (l : list A) : option A :=
  match l with
  | nil => None
  | cons x xs => if p x then Some x else find_opt p xs
  end.

(** [last_opt l] returns the last element, or None for empty. *)
Fixpoint last_opt {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | cons x nil => Some x
  | cons _ xs => last_opt xs
  end.

(** [nth_opt n l] returns the nth element, or None for out of bounds. *)
Fixpoint nth_opt {A : Type} (n : nat) (l : list A) : option A :=
  match l with
  | nil => None
  | cons x xs => if Nat.eqb n O then Some x else nth_opt (Nat.sub n 1) xs
  end.

(** [lookup_opt key l] looks up key in an association list. *)
Fixpoint lookup_opt (key : nat) (l : list (nat * nat)) : option nat :=
  match l with
  | nil => None
  | cons p xs =>
    if Nat.eqb (fst p) key then Some (snd p) else lookup_opt key xs
  end.

(** [map_opt f l] applies f and keeps only Some results. *)
Fixpoint map_opt {A B : Type} (f : A -> option B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs =>
    match f x with
    | None => map_opt f xs
    | Some y => cons y (map_opt f xs)
    end
  end.

(** [find_index p l] returns the index of the first match, or None. *)
Fixpoint find_index_aux {A : Type} (p : A -> bool) (l : list A) (i : nat) : option nat :=
  match l with
  | nil => None
  | cons x xs => if p x then Some i else find_index_aux p xs (S i)
  end.

Definition find_index {A : Type} (p : A -> bool) (l : list A) : option nat :=
  find_index_aux p l O.

End LoopifyOption.

Set Crane Loopify.
Crane Extraction "loopify_option" LoopifyOption.
