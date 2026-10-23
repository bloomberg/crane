(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A loop whose list parameter is kept by value and advanced to the tail
    of the cell it holds, where the tail is also read by a closure.

    Translation names the tail once, [const lst &a1_value = *a1], and the
    loop advanced by [_loop_l = a1_value]: an assignment from a reference
    into the cell [_loop_l] owns, which the assignment frees before it has
    read it.  A dereference was copied first; a reference to one is now
    too. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.
Set Crane NonAtomicRc.
Set Crane Reuse.

Module LoopifyShadowFromReference.

Inductive lst : Type := nil : lst | cons : nat -> lst -> lst.

Fixpoint suml (l : lst) : nat := match l with nil => 0 | cons x t => x + suml t end.

Definition twice (f : nat -> nat) (x : nat) : nat := f (f x).

Fixpoint g (l : lst) : lst :=
  match l with
  | nil => nil
  | cons x t => cons (twice (fun y => suml (cons y t)) x) (g t)
  end.

Fixpoint upto (n : nat) : lst := match n with O => nil | S k => cons n (upto k) end.

End LoopifyShadowFromReference.

Crane Extraction "loopify_shadow_from_reference" LoopifyShadowFromReference.
