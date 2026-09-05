From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Set Crane Loopify.

Module DeepTailRecursionOverflow.

(** A three-million-link value-type chain, built by a tail recursion and
    consumed by a non-tail one.  Both recursions have to become loops, and the
    chain's destructor has to drain its own spine, or the C++ stack overflows
    on any one of the three. *)
Inductive chain : Type := End_ : nat -> chain | Link : chain -> nat -> chain.

Fixpoint build (n : nat) (acc : chain) : chain :=
  match n with O => acc | S k => build k (Link acc n) end.

Fixpoint total_of (c : chain) : nat :=
  match c with End_ n => n | Link c' n => n + total_of c' end.

Definition deep : nat := total_of (build 3000000 (End_ 0)).

End DeepTailRecursionOverflow.
Crane Extraction "deep_tail_recursion_overflow" DeepTailRecursionOverflow.
