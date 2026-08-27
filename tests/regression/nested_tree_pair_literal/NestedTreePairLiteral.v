From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** A non-uniform (nested) inductive
    ([tree A := Lf : A -> tree A | Nd : tree (A * A) -> tree A]) has its type
    parameter erased, so a literal value built at [tree nat] passes a
    [std::pair] through the erased constructor. *)

Module NestedTreePairLiteral.
Inductive tree (A : Type) : Type := Lf : A -> tree A | Nd : tree (A * A)%type -> tree A.
Fixpoint size {A} (t : tree A) : nat :=
  match t with Lf _ _ => 1 | Nd _ u => 2 * size u end.
Definition sample : tree nat := Nd _ (Nd _ (Lf _ ((1,2),(3,4)))).
Definition go : nat := size sample.
End NestedTreePairLiteral.
Crane Extraction "nested_tree_pair_literal" NestedTreePairLiteral.
