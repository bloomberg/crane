(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** References that are only ever written.  Scalar replacement keeps a
    reference used only where it is created in a local, and a store into it
    nothing reads is dropped with it; what is left must not be a variable
    only ever set, which [-Wunused-but-set-variable] rejects:
    - [written_only]: a reference a loop helper writes and nothing reads;
    - [read_by_dead_store]: a loop parameter read only to initialise a
      reference nothing reads -- the parameter is then only ever assigned;
    - [written_in_branch]: a reference written in one branch of a
      conditional, read in neither;
    - [written_in_unused_branch]: the same where nothing reads the
      conditional's value either: what computes it still runs, without
      the store. *)

From Stdlib Require Import Arith.PeanoNat List.
From ITree Require Import Events.Exception ITree.
From Crane Require Import Mapping.NatIntStd Monads.Error Monads.ITree Monads.STMonad.
Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section S.
  Context {R : STRefs}.
  Notation E0 := (STEvent R (fun _ : nat => nat) +' exceptE Err).

  Definition written_only : itree E0 nat :=
    r <- newSTRef 1;;
    let fix go (k : nat) (p : STRef nat) : itree E0 nat :=
      match k with
      | O => Ret 7
      | Datatypes.S k' => writeSTRef p (k' * 2);; go k' p
      end in
    go 3 r.

  Definition read_by_dead_store : itree E0 nat :=
    let fix go (k acc : nat) : itree E0 nat :=
      match k with
      | O => Ret k
      | Datatypes.S k' => r <- newSTRef acc;; go k' (acc + 1)
      end in
    go 4 0.

  Definition written_in_branch (b : bool) : itree E0 nat :=
    r <- newSTRef 0;;
    x <- (if b then writeSTRef r 5;; Ret 1 else Ret 2);;
    Ret (x + 10).

  Definition written_in_unused_branch (b : bool) : itree E0 nat :=
    r <- newSTRef 0;;
    s <- newSTRef 3;;
    x <- (if b then writeSTRef r 5;; v <- readSTRef s;; writeSTRef s (v + 1);; Ret 1 else Ret 2);;
    readSTRef s.
End S.

Module StDeadStores.
  Definition written_only : nat := run_st (@written_only cpp_refs).
  Definition read_by_dead_store : nat := run_st (@read_by_dead_store cpp_refs).
  Definition written_in_branch (b : bool) : nat := run_st (@written_in_branch cpp_refs b).
  Definition written_in_unused_branch (b : bool) : nat := run_st (@written_in_unused_branch cpp_refs b).
End StDeadStores.

Set Crane Loopify.
Crane Extraction "st_dead_stores" StDeadStores.
