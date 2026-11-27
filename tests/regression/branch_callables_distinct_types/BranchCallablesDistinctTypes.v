From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Two branches producing function values of different C++ types, with no
    common type spelled for the result (the pair-of-lambdas form in
    branch_pairs_of_lambdas is fixed):
    - [t]: in a [fold_left] step, one branch returns a composed let-lambda,
      the other a plain lambda: "return type '(lambda ...)' must match
      previous return type '(lambda ...)'".
    - [u]: a class method ([sz]) in one [if] branch and a lambda from a match
      in the other, as a constructor argument: "incompatible operand types
      ('uint64_t (uint64_t)' and '(lambda ...)')". *)
Module BranchCallablesDistinctTypes.

Record pt : Type := mkpt { px : nat; py : bool }.

Definition t : nat :=
  (fun w : nat -> pt => px (w 0) + px (w 3))
  (fold_left (fun (acc : nat -> pt) (e : bool) =>
     if negb e then (let cf := (fun _ : nat => mkpt 1 true) in let cg := (fun k : nat => k) in fun c : nat => cf (cg c))
     else (fun _ : nat => mkpt 2 true)) [true] (fun _ : nat => mkpt 0 true)).

Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_nat : Sz nat := { sz n := n }.
Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
Arguments PLeaf {A}.
Arguments PNode {A} _ _ _.

Definition f (b : bool) (l : list nat) : ptree (nat -> nat) :=
  PNode PLeaf (if b then sz else (match l with [] => (fun _ : nat => 0) | _ :: _ => (fun k : nat => 4) end)) PLeaf.

Definition u : nat :=
  (match f false [1] with PNode _ g _ => g 7 | PLeaf => 0 end) +
  (match f true [] with PNode _ g _ => g 7 | PLeaf => 0 end).

End BranchCallablesDistinctTypes.

Crane Extraction "branch_callables_distinct_types" BranchCallablesDistinctTypes.
