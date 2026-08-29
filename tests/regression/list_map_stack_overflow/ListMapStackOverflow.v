From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ListMapStackOverflow.
  (** The [List] methods Crane generates for the mapped stdlib list are
      structural recursion over the list: emitted as plain recursion they
      take one C++ stack frame per cell, and [List<A>::map] blows the
      stack on a 200 000-element list.  Unlike a user [Fixpoint] they are
      generated members of the mapped [List] type, with no name to hang a
      [Crane Loopify] on, so they are loopified by default.
  *)
  (** A tail-recursive builder, loopified below, so that constructing the
      list itself is stack-safe: only the generated [List] method under test
      can overflow. *)
  Fixpoint bld (n : nat) (acc : list nat) : list nat :=
    match n with 0 => acc | S j => bld j (j :: acc) end.

  Definition run (k : nat) : nat :=
    fold_left Nat.add (map (fun x => x + 1) (bld (k + 200000) [])) 0.
End ListMapStackOverflow.

Crane Loopify ListMapStackOverflow.bld.

Crane Extraction "list_map_stack_overflow" ListMapStackOverflow.
