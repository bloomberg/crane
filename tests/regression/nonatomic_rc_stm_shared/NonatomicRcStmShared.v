(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane NonAtomicRc] is a promise that the program's values are used
    from one thread at a time.  A unit using [Monads.STM] breaks it even
    though it starts no thread itself: transactional memory exists to be
    shared by the threads its caller starts.  The driver pushes onto one
    TVar-held list from several [std::thread]s, so every [readTVar] copies a
    count another thread is updating -- with a non-atomic count, cells are
    freed while still reachable.

    Crane withholds the request from such a unit (it keeps
    [std::shared_ptr] and warns [crane-non-atomic-rc-concurrent]), and the
    header checks [crane::rc_is_atomic] after its includes. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO Monads.STM.
Set Crane NonAtomicRc.

Module NonatomicRcStmShared.

Open Scope itree_scope.

Inductive lst : Set := Nil : lst | Cons : nat -> lst -> lst.

Fixpoint len (l : lst) : nat :=
  match l with Nil => 0 | Cons _ r => S (len r) end.

Definition make : itree ioE (TVar lst) := atomically (newTVar Nil).

Definition push (t : TVar lst) (n : nat) : itree ioE unit :=
  atomically (l <- readTVar t ;; writeTVar t (Cons n l)).

Definition size (t : TVar lst) : itree ioE nat :=
  atomically (l <- readTVar t ;; Ret (len l)).

End NonatomicRcStmShared.

Crane Extraction "nonatomic_rc_stm_shared" NonatomicRcStmShared.
