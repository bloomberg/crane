(** Found by Ephyra round 23. [Crane Bake] of a [PrimArray.array] whose
    elements are, or hold, inductive nodes ([Mapping.Std]: a
    [persistent_array] of [List], of a user inductive, of an option of
    one, of an array of them).
    Expected: baked, [total = 2 + 3 + 9 + 0 + 4 + 3 = 21].
    Fixed: the bake driver failed: [lists] and [nodes] with "crane::bake: a
    node named before it is written", [leaves] with "crane::bake: a null
    pointer in the value", [make 2 []] with exit code 118 and no message.
    The image writer tells nodes apart by address and keeps a pointer to
    each node it has still to write, but it walked a [persistent_array]
    through [get], which returns a copy: the pointer dangled, and the row
    was written under the copy's address, not the one [put] looked up. It
    now walks the array in place ([persistent_array::ref]); every other
    container hook (optional, pair, tuple, sequence, shared array, handle)
    already walked by reference. *)
From Crane Require Import Mapping.NatInt Mapping.Std.
From Crane Require Import Extraction.
From Stdlib Require Import List ZArith Uint63.
From Corelib Require Import PrimArray.
Import ListNotations.

Module BakeArrayOfNodes.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.

Definition lists : PrimArray.array (list nat) := PrimArray.make 2%uint63 [1; 2].
Definition nodes : PrimArray.array tree := PrimArray.make 2%uint63 (Node Leaf 3 Leaf).
Definition leaves : PrimArray.array tree := PrimArray.make 2%uint63 Leaf.
Definition empties : PrimArray.array (list nat) := PrimArray.make 3%uint63 [].
Definition opts : PrimArray.array (option tree) :=
  PrimArray.make 2%uint63 (Some (Node Leaf 4 Leaf)).
Definition nested : PrimArray.array (PrimArray.array tree) := PrimArray.make 2%uint63 nodes.

Definition root (t : tree) : nat := match t with Leaf => 9 | Node _ n _ => n end.

Definition total : nat :=
  List.length (PrimArray.get lists 1%uint63) + root (PrimArray.get nodes 0%uint63)
  + root (PrimArray.get leaves 1%uint63)
  + List.length (PrimArray.get empties 2%uint63)
  + match PrimArray.get opts 1%uint63 with Some t => root t | None => 0 end
  + root (PrimArray.get (PrimArray.get nested 1%uint63) 0%uint63).

End BakeArrayOfNodes.

Crane Bake BakeArrayOfNodes.lists BakeArrayOfNodes.nodes BakeArrayOfNodes.leaves
  BakeArrayOfNodes.empties BakeArrayOfNodes.opts BakeArrayOfNodes.nested.
Crane Extraction "bake_array_of_nodes" BakeArrayOfNodes.
