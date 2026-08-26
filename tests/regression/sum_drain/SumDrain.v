(* Regression: an inductive whose recursion is nested inside [sum] gets no iterative
   drain, so deep values overflow the stack when destroyed.

   Crane emits a worklist-based [~T()] when it recognises the shape of the
   mediating type -- a direct self-reference, a cons-list, or a single-
   constructor wrapper.  [nat + t] is none of those, so destruction recurses
   ~t -> ~Sum::Inr -> ~t -> ... once per level.

   Observed: 300k levels build fine; [delete] segfaults (ASan: stack-overflow
   in the Sum variant destructor). *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Set Crane Loopify.
Module SumDrain.
Inductive t : Type := N : (nat + t) -> t.
Fixpoint build (n : nat) (acc : t) : t :=
  match n with O => acc | S m => build m (N (inr acc)) end.
Fixpoint depth (x : t) : nat :=
  match x with N s => match s with inl _ => 0 | inr u => S (depth u) end end.
Definition go (n : nat) : nat := depth (build n (N (inl 0))).
End SumDrain.
Crane Extraction "sum_drain" SumDrain.
