(* WIP: an inductive whose recursive occurrence is NESTED inside another
   inductive gets no drain destructor, so deep values blow the stack when
   they are destroyed.

   [tree] recurses through [lst tree] rather than through a direct
   self-reference.  Crane generates an iterative drain [~lst()] that walks the
   [lst] spine (the [a1] field) with a per-cell [use_count() == 1] check, but
   it never descends into the [a0] element, and no [~tree()] is generated at
   all.  Destroying a degenerate chain therefore recurses
   ~lst<tree> -> ~tree -> ~lst<tree> -> ... once per level.

   Observed: building and summing a 5000-deep tree both succeed; the
   subsequent destruction segfaults (ASan: stack-overflow). *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module NestedInductiveNoDrain.

Inductive lst (A : Type) : Type :=
| nil : lst A
| cons : A -> lst A -> lst A.
Arguments nil {A}.
Arguments cons {A} _ _.

(* recursive occurrence is NESTED inside another inductive *)
Inductive tree : Type := node : nat -> lst tree -> tree.

Fixpoint spine (n : nat) (acc : tree) : tree :=
  match n with O => acc | S m => spine m (node n (cons acc nil)) end.

Fixpoint tsum (t : tree) : nat :=
  match t with
  | node x l =>
      x + (fix go (m : lst tree) : nat :=
             match m with nil => 0 | cons u r => tsum u + go r end) l
  end.

Definition go (n : nat) : nat := tsum (spine n (node 0 nil)).

End NestedInductiveNoDrain.

Crane Extraction "nested_inductive_no_drain" NestedInductiveNoDrain.
