(* Regression: loopifying a mutually recursive pair of functions builds frames whose
   fields are typed [const T*] but constructs them from values.

   [tsum]/[fsum] are inlined into one another's loop.  The generated frame
   [_Enter] declares its tree field as [const tree*] (the pointer-shadow
   optimisation), yet the emplace passes a dereferenced [shared_ptr]:

     _stack.emplace_back(_Enter{*_inl_a0, _inl_acc});

     error: no viable conversion from 'element_type' (aka 'tree')
            to 'const tree *'

   The surrounding code also rebinds [_inl_f] inside the branch that already
   has an [_inl_f] in scope, so the shadowing needs looking at too. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Set Crane Loopify.
Module MutualLoopifyAcc.
Inductive tree : Type := leaf : nat -> tree | node : forest -> tree
with forest : Type := fnil : forest | fcons : tree -> forest -> forest.
Fixpoint tsum (acc : nat) (t : tree) : nat :=
  match t with leaf n => acc + n | node f => fsum acc f end
with fsum (acc : nat) (f : forest) : nat :=
  match f with fnil => acc | fcons t r => fsum (tsum acc t) r end.
Fixpoint chain (n : nat) (acc : tree) : tree :=
  match n with O => acc | S m => chain m (node (fcons acc (fcons (leaf 1) fnil))) end.
Definition go (n : nat) : nat := tsum 0 (chain n (leaf 0)).
End MutualLoopifyAcc.
Crane Extraction "mutual_loopify_acc" MutualLoopifyAcc.
