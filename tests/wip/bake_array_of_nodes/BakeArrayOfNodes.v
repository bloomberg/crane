(** Found by Ephyra round 23. [Crane Bake] of a [PrimArray.array] whose
    elements are inductive nodes ([Mapping.Std]: a [persistent_array] of
    [List] or of a user inductive). docs/Crane-Bake.md says a
    [persistent_array] is its length and elements (default after the
    length); arrays of scalars, options, pairs and arrays bake fine.
    Expected: baked, [total = 2 + 3 + 9 = 14].
    Actual: the bake driver fails. Each constant alone: [lists]
    ([make 2 [1;2]]) and [nodes] ([make 2 (Node Leaf 3 Leaf)]) give
    "crane::bake: a node named before it is written"; [leaves]
    ([make 2 Leaf]) gives "crane::bake: a null pointer in the value";
    [make 2 []] exits with code 118 and no message. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Import Extraction.
From Stdlib Require Import List ZArith Uint63.
From Corelib Require Import PrimArray.
Import ListNotations.

Module BakeArrayOfNodes.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.

Definition lists : PrimArray.array (list nat) := PrimArray.make 2%uint63 [1; 2].
Definition nodes : PrimArray.array tree := PrimArray.make 2%uint63 (Node Leaf 3 Leaf).
Definition leaves : PrimArray.array tree := PrimArray.make 2%uint63 Leaf.

Definition root (t : tree) : nat := match t with Leaf => 9 | Node _ n _ => n end.

Definition total : nat :=
  List.length (PrimArray.get lists 1%uint63) + root (PrimArray.get nodes 0%uint63)
  + root (PrimArray.get leaves 1%uint63).

End BakeArrayOfNodes.

Crane Bake BakeArrayOfNodes.lists BakeArrayOfNodes.nodes BakeArrayOfNodes.leaves.
Crane Extraction "bake_array_of_nodes" BakeArrayOfNodes.
