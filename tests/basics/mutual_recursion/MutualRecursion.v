(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test mutually recursive functions *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module MutualRecursion.

(* Classic even/odd mutual recursion *)
Fixpoint is_even (n : nat) : bool :=
  match n with
  | O => true
  | S m => is_odd m
  end
with is_odd (n : nat) : bool :=
  match n with
  | O => false
  | S m => is_even m
  end.

(* Tree structure for mutual recursion *)
Inductive tree (A : Type) : Type :=
| Leaf : A -> tree A
| Node : forest A -> tree A
with forest (A : Type) : Type :=
| Empty : forest A
| Trees : tree A -> forest A -> forest A.

Arguments Leaf {A} _.
Arguments Node {A} _.
Arguments Empty {A}.
Arguments Trees {A} _ _.

(* Mutual recursion over mutually inductive types *)
Fixpoint tree_size {A : Type} (t : tree A) : nat :=
  match t with
  | Leaf _ => 1
  | Node f => forest_size f
  end
with forest_size {A : Type} (f : forest A) : nat :=
  match f with
  | Empty => 0
  | Trees t rest => Nat.add (tree_size t) (forest_size rest)
  end.

(* More complex mutual recursion *)
Fixpoint tree_sum (t : tree nat) : nat :=
  match t with
  | Leaf n => n
  | Node f => forest_sum f
  end
with forest_sum (f : forest nat) : nat :=
  match f with
  | Empty => 0
  | Trees t rest => Nat.add (tree_sum t) (forest_sum rest)
  end.

(* Test values *)
Definition test_even_0 := is_even 0.
Definition test_even_4 := is_even 4.
Definition test_odd_3 := is_odd 3.
Definition test_odd_4 := is_odd 4.

Definition simple_tree : tree nat := Node (Trees (Leaf 1) (Trees (Leaf 2) Empty)).
Definition nested_tree : tree nat :=
  Node (Trees (Node (Trees (Leaf 3) Empty))
        (Trees (Leaf 4) Empty)).

Definition test_size_simple := tree_size simple_tree.
Definition test_size_nested := tree_size nested_tree.
Definition test_sum_simple := tree_sum simple_tree.
Definition test_sum_nested := tree_sum nested_tree.

End MutualRecursion.

Crane Extraction "mutual_recursion" MutualRecursion.
