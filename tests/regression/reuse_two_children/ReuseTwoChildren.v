(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Perceus reuse for a node with two children, as a map's is: updating the
    value at a key rebuilds the node it is at, and the rebuild recycles the
    node's first child's cell.  Under [BoxedFields], so that the other child
    is behind a pointer and the value in a [crane::field], and both are read
    out of the recycled node the way they are stored. *)

From Stdlib Require Import PeanoNat.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ReuseTwoChildren.

Inductive tree (A : Type) : Type :=
| Leaf : tree A
| Node : tree A -> nat -> A -> tree A -> tree A.
Arguments Leaf {A}. Arguments Node {A}.

Fixpoint insert {A} (k : nat) (v : A) (t : tree A) : tree A :=
  match t with
  | Leaf => Node Leaf k v Leaf
  | Node l k' v' r =>
      if Nat.ltb k k' then Node (insert k v l) k' v' r
      else if Nat.ltb k' k then Node l k' v' (insert k v r)
      else Node l k v r
  end.

Fixpoint find {A} (k : nat) (t : tree A) : option A :=
  match t with
  | Leaf => None
  | Node l k' v r =>
      if Nat.ltb k k' then find k l
      else if Nat.ltb k' k then find k r
      else Some v
  end.

Fixpoint size {A} (t : tree A) : nat :=
  match t with Leaf => 0 | Node l _ _ r => 1 + size l + size r end.

Definition t0 : tree nat :=
  insert 5 50 (insert 3 30 (insert 8 80 (insert 1 10 (insert 4 40 Leaf)))).
Definition t1 : tree nat := insert 3 33 (insert 8 88 t0).

Definition result : nat :=
  match find 3 t1, find 8 t1, find 5 t1 with
  | Some a, Some b, Some c => a + b + c + size t1
  | _, _, _ => 0
  end.

End ReuseTwoChildren.

Set Crane NonAtomicRc.
Set Crane Reuse.
Set Crane BoxedFields.
Crane Extraction "reuse_two_children" ReuseTwoChildren.
