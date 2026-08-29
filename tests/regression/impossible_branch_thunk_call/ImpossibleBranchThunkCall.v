From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ImpossibleBranchThunkCall.
  (** Matching on an indexed inductive at a fixed index leaves a branch that
      is impossible in Rocq.  Applying its absurd eliminator is itself
      unreachable, so the branch must emit the throw alone rather than calling
      the throwing thunk's [std::any] result. *)
  Inductive tagged : bool -> Type :=
  | TN : nat -> tagged true
  | TL : list nat -> tagged false.

  Definition val (t : tagged true) : nat := match t with TN n => n end.
  Definition len (t : tagged false) : nat := match t with TL l => length l end.

  Definition run (k : nat) : nat := val (TN (k + 3)) + len (TL [1; 2]).
End ImpossibleBranchThunkCall.

Crane Extraction "impossible_branch_thunk_call" ImpossibleBranchThunkCall.
