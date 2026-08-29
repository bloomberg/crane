From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ListFoldLeftStackOverflow.
  (** The [List] methods Crane generates for the mapped stdlib list are
      emitted as plain non-tail recursion, one C++ stack frame per cell.  On a
      200 000-element list [List<A>::fold_left] overflows the stack (ASan reports
      [stack-overflow]).  Unlike a user [Fixpoint], these are generated members
      of the mapped [List] type, so [Crane Loopify] cannot be applied to
      them. *)
  (** A tail-recursive builder, loopified below, so that constructing the
      list itself is stack-safe: only the generated [List] method under test
      can overflow. *)
  Fixpoint bld (n : nat) (acc : list nat) : list nat :=
    match n with 0 => acc | S j => bld j (j :: acc) end.

  Definition run (k : nat) : nat := fold_left Nat.add (bld (k + 200000) []) 0.
End ListFoldLeftStackOverflow.

Crane Loopify ListFoldLeftStackOverflow.bld.

Crane Extraction "list_fold_left_stack_overflow" ListFoldLeftStackOverflow.
