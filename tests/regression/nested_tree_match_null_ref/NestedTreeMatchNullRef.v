From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.
Set Crane Reuse.
Set Crane SharedVariant.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    Memory safety: at run time UBSan reports "reference binding to null pointer of type 'const tree'" (abort). [t_5] applies the class method [sz] to a match on a tree built from a match on a record update, whose [Node] branch re-matches its right subtree and stores it again. *)
Module NestedTreeMatchNullRef.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Fixpoint tree_obs (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l v r => (tree_obs l * 7 + v + tree_obs r * 3) mod 10007
  end.
Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_tree : Sz tree := { sz := tree_obs }.
Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
CoInductive stream : Type := SCons : nat -> stream -> stream.
Definition st (A : Type) : Type := nat -> A * nat.
Record r3 : Type := mkr3 { ra : nat; rb : list nat; rc : bool }.

Definition t_5 : nat :=
  (sz (match (match (let rr23 := (mkr3 0%nat [] true) in {| ra := ra rr23; rb := (@nil nat); rc := negb (rc rr23) |}) with mkr3 ma25 mb26 mc27 => (Node Leaf 0%nat (Node Leaf ma25 Leaf)) end) with Leaf => Leaf | Node tl28 tv29 tr30 => (Node (match tr30 with Leaf => Leaf | Node tl33 tv34 tr35 => (Node Leaf 0%nat Leaf) end) 0%nat tr30) end)).
End NestedTreeMatchNullRef.

Crane Extraction "nested_tree_match_null_ref" NestedTreeMatchNullRef.
