(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

(** A tail-recursive method whose recursive call passes, as the receiver, a
    binder of a match on a value the turn makes.

    The loop keeps the receiver as a pointer, [_loop_self].  A receiver made
    in the turn must be parked in a local outliving the loop first, and the
    C++ reading that decided this saw only receivers spelled as temporaries:
    [inner] is a reference into the result of [wrap], so the loop pointed at
    it, and the next turn read it after that result was destroyed -- a
    heap-use-after-free.  The turns whose receiver no parameter of the loop
    gives are now the recursion plan's ({!Control_ir.rebuilt}), and these
    park. *)
Module LoopifyReceiverFromTemporary.

Inductive box (A : Type) : Type := B : A -> box A.
Arguments B {A} _.

Inductive t : Type := L | N : box t -> t.

Definition wrap (x : t) : t := N (B (N (B x))).

Fixpoint walk (n : nat) (acc : t) (k : nat) {struct n} : nat :=
  match n with
  | O => k
  | S m => match wrap acc with N (B inner) => walk m inner (S k) | L => k end
  end.

Definition go (n : nat) : nat := walk n L 0.

End LoopifyReceiverFromTemporary.

Set Crane Loopify.
Crane Extraction "loopify_receiver_from_temporary" LoopifyReceiverFromTemporary.
