From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module NameClashMatchMatch.

(** Test: match on the result of another match, both non-trivial.
    The inner match creates an IIFE, the outer match also creates an IIFE.
    Both might generate _sv/_m variable names that could clash. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

(** Returns a subtree based on a direction. *)
Inductive dir : Type :=
| GoLeft : dir
| GoRight : dir.

Definition choose_subtree (d : dir) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l _ r =>
    match d with
    | GoLeft => l
    | GoRight => r
    end
  end.

(** Match on the result of choose_subtree (which itself contains a match). *)
Definition subtree_value (d : dir) (t : tree) : nat :=
  match choose_subtree d t with
  | Leaf => 0
  | Node _ v _ => v
  end.

(** Inline match-on-match: both matches are expressions. *)
Definition inline_match_match (d : dir) (t : tree) : nat :=
  match (match d with GoLeft => t | GoRight => Leaf end) with
  | Leaf => 100
  | Node _ v _ => v
  end.

(** Two matches on the same scrutinee. *)
Definition double_match (t : tree) : nat :=
  let a := match t with Leaf => 0 | Node _ v _ => v end in
  let b := match t with Leaf => 1 | Node l _ _ => match l with Leaf => 2 | Node _ v _ => v end end in
  a + b.

(** Match where the scrutinee is a function call that returns an inductive,
    and the result is used in another match. *)
Definition chained (t : tree) : nat :=
  match (match t with
         | Leaf => Node Leaf 42 Leaf
         | Node l v r => Node r v l
         end) with
  | Leaf => 0
  | Node _ v _ => v
  end.

End NameClashMatchMatch.

Crane Extraction "name_clash_match_match" NameClashMatchMatch.
