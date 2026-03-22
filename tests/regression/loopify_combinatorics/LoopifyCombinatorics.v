(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
Require Crane.Extraction.

(** Consolidated combinatorial algorithms. *)
Module LoopifyCombinatorics.

(* ========== COMBINATORIAL ALGORITHMS ========== *)

(** [remove x l] removes first occurrence of x from list. *)
Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons y ys => if Nat.eqb x y then ys else cons y (remove x ys)
  end.

(** Helper: prepend x to each list in lsts. *)
Fixpoint map_cons (x : nat) (lsts : list (list nat)) : list (list nat) :=
  match lsts with
  | nil => nil
  | cons p ps => cons (cons x p) (map_cons x ps)
  end.

(** [perms_choices_fuel fuel choices orig] generates permutations by iterating
    over choices.  Single self-recursive function that handles both the choice
    iteration and the recursive subproblem, enabling full loopification.
    The match on [remaining] is hoisted out of the let-binding so that all
    recursive calls appear at the top level of each branch. *)
Fixpoint perms_choices_fuel (fuel : nat) (choices orig : list nat)
                            : list (list nat) :=
  match fuel with
  | O => nil
  | S f =>
    match choices with
    | nil => nil
    | cons x xs =>
      let remaining := remove x orig in
      match remaining with
      | nil =>
        app (map_cons x (cons nil nil))
                    (perms_choices_fuel f xs orig)
      | _ =>
        app (map_cons x (perms_choices_fuel f remaining remaining))
                    (perms_choices_fuel f xs orig)
      end
    end
  end.

(** [permutations_fuel fuel l] generates all permutations of a list. *)
Definition permutations_fuel (fuel : nat) (l : list nat) : list (list nat) :=
  match l with
  | nil => cons nil nil
  | _ => perms_choices_fuel fuel l l
  end.

Fixpoint len_list (l : list nat) : nat :=
  match l with
  | nil => O
  | cons _ xs => S (len_list xs)
  end.

Fixpoint factorial_impl (n : nat) : nat :=
  match n with
  | O => 1
  | S m => Nat.mul n (factorial_impl m)
  end.

Definition permutations (l : list nat) : list (list nat) :=
  permutations_fuel (factorial_impl (len_list l)) l.

(** [subsequences l] generates all subsequences (subsets preserving order). *)
Fixpoint subsequences (l : list nat) : list (list nat) :=
  match l with
  | nil => cons nil nil
  | cons x xs =>
    let rest := subsequences xs in
    let fix map_prepend lst :=
      match lst with
      | nil => nil
      | cons s ss => cons (cons x s) (map_prepend ss)
      end
    in app rest (map_prepend rest)
  end.

(** Helper for cartesian product. *)
Fixpoint map_pairs (y : nat) (l : list nat) : list (nat * nat) :=
  match l with
  | nil => nil
  | cons x xs => cons (x, y) (map_pairs y xs)
  end.

(** [cartesian l1 l2] Cartesian product of two lists. *)
Fixpoint cartesian (l1 l2 : list nat) : list (nat * nat) :=
  match l2 with
  | nil => nil
  | cons y ys => app (map_pairs y l1) (cartesian l1 ys)
  end.

(** [power_set l] generates the power set (all subsets). *)
Fixpoint power_set (l : list nat) : list (list nat) :=
  match l with
  | nil => cons nil nil
  | cons x xs =>
    let rest := power_set xs in
    let fix map_add_x lst :=
      match lst with
      | nil => nil
      | cons s ss => cons (cons x s) (map_add_x ss)
      end
    in app rest (map_add_x rest)
  end.

(** [insert_everywhere x l] inserts x at every position in l. *)
Fixpoint insert_everywhere (x : nat) (l : list nat) : list (list nat) :=
  match l with
  | nil => cons (cons x nil) nil
  | cons y ys =>
    let rest := insert_everywhere x ys in
    let fix prepend_y lsts :=
      match lsts with
      | nil => nil
      | cons lst lsts' => cons (cons y lst) (prepend_y lsts')
      end
    in cons (cons x l) (prepend_y rest)
  end.

(** Helper: check if element is in list. *)
Fixpoint elem (x : nat) (l : list nat) : bool :=
  match l with
  | nil => false
  | cons y ys => orb (Nat.eqb x y) (elem x ys)
  end.

(** Helper: list length. *)
Fixpoint len_impl (l : list nat) : nat :=
  match l with
  | nil => O
  | cons _ xs => S (len_impl xs)
  end.

(** [dedup l] removes all duplicates (keeps first occurrence). *)
Fixpoint dedup_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons x xs =>
      let rest := dedup_fuel f xs in
      if elem x rest then rest else cons x rest
    end
  end.

Definition dedup (l : list nat) : list nat :=
  dedup_fuel (len_impl l) l.

End LoopifyCombinatorics.

Set Crane Loopify.
Crane Extraction "loopify_combinatorics" LoopifyCombinatorics.
