From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A polymorphic definition with a class constraint and a [ptree A]
    parameter is turned into a method of [ptree<A>], but its constraint is
    still written over the free function's template parameter:
    [requires Sz<_tcI0, T1>] inside the class, "use of undeclared identifier
    'T1'".  Fragile: the unrelated declarations (tree, tree_obs, stream) kept
    from the generated prelude are needed to trigger it. *)
Module MethodifiedConstraintTparam.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Fixpoint tree_obs (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l v r => Nat.modulo (tree_obs l * 7 + v + tree_obs r * 3) 10007
  end.
Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_nat : Sz nat := { sz n := n }.
Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
Arguments PLeaf {A}.
Arguments PNode {A} _ _ _.
CoInductive stream : Type := SCons : nat -> stream -> stream.

Definition f2 {A : Type} `{Sz A} (a9 : A) (a10 : ptree A) (a11 : A) : option A :=
  Some a9.

Definition t : nat := match f2 4 PLeaf 5 with Some x => x | None => 0 end.

End MethodifiedConstraintTparam.

Crane Extraction "methodified_constraint_tparam" MethodifiedConstraintTparam.
