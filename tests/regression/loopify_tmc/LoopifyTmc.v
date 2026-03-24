(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** Tests for Tail Modulo Cons (TMC) loopification optimization.
    Functions where the recursive call is wrapped in a single constructor
    should be optimized to use O(1) extra space via destination-passing style. *)
Module LoopifyTmc.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

(** [app l1 l2] appends two lists. Basic TMC pattern: cons head (app tail l2). *)
Fixpoint app {A : Type} (l1 : list A) (l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (app xs l2)
  end.

(** [map f l] applies f to every element. TMC with element transform. *)
Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
  end.

(** [filter f l] keeps elements satisfying f. Mixed tail + TMC branches. *)
Fixpoint filter {A : Type} (f : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => if f x then cons x (filter f xs) else filter f xs
  end.

(** [snoc l x] appends x at the end. TMC, base case allocates a cell. *)
Fixpoint snoc {A : Type} (l : list A) (x : A) : list A :=
  match l with
  | nil => cons x nil
  | cons h t => cons h (snoc t x)
  end.

(** [replicate n x] creates n copies of x. Nat recursion producing list. *)
Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | O => nil
  | S m => cons x (replicate m x)
  end.

(** [range lo hi] creates [lo, lo+1, ..., hi-1]. *)
Fixpoint range (lo hi : nat) : list nat :=
  match hi with
  | O => nil
  | S hi' => if Nat.leb lo hi' then cons hi' (range lo hi') else nil
  end.

(** [zip_with f l1 l2] combines two lists element-wise. Two varying params. *)
Fixpoint zip_with {A B C : Type} (f : A -> B -> C)
  (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | cons x xs, cons y ys => cons (f x y) (zip_with f xs ys)
  | _, _ => nil
  end.

(** [prefix_sums acc l] computes running prefix sums. *)
Fixpoint prefix_sums (acc : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs => let s := Nat.add acc x in cons s (prefix_sums s xs)
  end.

(** [stutter l] duplicates each element: [1,2] -> [1,1,2,2]. Nested TMC. *)
Fixpoint stutter {A : Type} (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => cons x (cons x (stutter xs))
  end.

End LoopifyTmc.

Set Crane Loopify.
Crane Extraction "loopify_tmc" LoopifyTmc.
