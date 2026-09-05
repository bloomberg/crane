From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.


Module DeepTailRecursionOverflow.

(** A plainly tail-recursive builder over a deep value-type inductive still
    recurses in the generated C++ (and so does the resulting move-constructor
    chain) unless [Set Crane Loopify] is in effect. *)
Inductive chain : Type := End_ : nat -> chain | Link : chain -> nat -> chain.

Fixpoint build (n : nat) (acc : chain) : chain :=
  match n with O => acc | S k => build k (Link acc n) end.

Fixpoint total_of (c : chain) : nat :=
  match c with End_ n => n | Link c' n => n + total_of c' end.

Definition deep : nat := total_of (build 3000000 (End_ 0)).

End DeepTailRecursionOverflow.
Crane Extraction "deep_tail_recursion_overflow" DeepTailRecursionOverflow.
