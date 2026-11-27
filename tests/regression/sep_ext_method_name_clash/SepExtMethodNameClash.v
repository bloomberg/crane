(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A function emitted as a method of its inductive's struct keeps clear of
    the members that struct generates: [clone], and the factory [leaf] of
    constructor [Leaf].  Under separate extraction the method registry is
    built once for the whole program, before the units, and each unit must
    still be told which constants are methods. *)

From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint clone (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l n r => clone l + n + clone r
  end.

Definition leaf (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node _ _ _ => 0
  end.

Definition sample : tree := Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf).

Definition total : nat := clone sample + leaf sample + leaf Leaf.

Crane Separate Extraction total.
