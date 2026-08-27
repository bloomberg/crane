(* WIP: loopify does not fire when the recursive call is wrapped in a single-field box constructor on the receiver, so mk recurses in C++ and overflows the stack at depth 200000. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Set Crane Loopify.
Module LoopifyWrapperReceiver.
Inductive box (A : Type) : Type := B : A -> box A.
Arguments B {A} _.
Inductive t : Type := L | N : box t -> t.
Fixpoint build (n : nat) (acc : t) : t := match n with O => acc | S m => build m (N (B acc)) end.
Definition mk (n : nat) : t := build n L.
End LoopifyWrapperReceiver.
Crane Extraction "loopify_wrapper_receiver" LoopifyWrapperReceiver.
