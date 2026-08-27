From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** WIP: A non-uniform (nested) inductive `tree A := Lf : A -> tree A | Nd : tree (A * A) -> tree A`
    builds a literal value: the erased-parameter constructor still expects
    `uint64_t` where a `std::pair<uint64_t, uint64_t>` is supplied. *)

Module NestedTreePairLiteral.
Inductive tree (A : Type) : Type := Lf : A -> tree A | Nd : tree (A * A)%type -> tree A.
Fixpoint size {A} (t : tree A) : nat :=
  match t with Lf _ _ => 1 | Nd _ u => 2 * size u end.
Definition sample : tree nat := Nd _ (Nd _ (Lf _ ((1,2),(3,4)))).
Definition go : nat := size sample.
End NestedTreePairLiteral.
Crane Extraction "nested_tree_pair_literal" NestedTreePairLiteral.
