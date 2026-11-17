(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Under the default pointer, [std::shared_ptr], a node rebuilt around a
    child read out of a matched value shares that child's cell, as OCaml
    shares the pointer, instead of copying the child into a new cell: an
    insertion allocates only the nodes on its path.  A child that is a
    constructor without fields shares one cell with every other such child,
    as OCaml's immediates do. *)

From Stdlib Require Import PeanoNat.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module SharedChildCells.

Inductive tree := Leaf | Node (l : tree) (k : nat) (r : tree).

Fixpoint insert (x : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf x Leaf
  | Node l k r =>
    if x <? k then Node (insert x l) k r
    else if k <? x then Node l k (insert x r)
    else t
  end.

Fixpoint sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l k r => sum l + k + sum r
  end.

(** Swaps the children: both are fields read out of the matched value. *)
Definition mirror_root (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l k r => Node r k l
  end.

End SharedChildCells.

Crane Extraction "shared_child_cells" SharedChildCells.
