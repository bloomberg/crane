(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO Monads.STM.

From Stdlib Require Import List Arith.

Import ListNotations.
Set Implicit Arguments.
Set Primitive Projections.

Module stmtest.

(* A guarded read that retries if a predicate fails *)
Definition readOrRetry {A} (tv : TVar A) (ok : A -> bool) : itree stmE A :=
  x <- readTVar tv ;;
  if ok x then Ret x else retry.

(* === Tests === *)

(* 1) Basic: create a TVar, read, write, read; returns 1 *)
Definition stm_basic_counter (_ : unit) : itree stmE nat :=
  c <- newTVar 0 ;;
  writeTVar c 1 ;;
  readTVar c.

Definition io_basic_counter : itree ioE nat :=
  atomically (stm_basic_counter tt).

(* 2) Increment test: write = read + 1; returns x+1 *)
Definition stm_inc (x : nat) : itree stmE nat :=
  c <- newTVar x ;;
  modifyTVar c (fun n => S n) ;;
  readTVar c.

Definition io_inc (x : nat) : itree ioE nat :=
  atomically (stm_inc x).

(* 3) Read-your-own-writes and sequencing; returns x + (x) = 2x *)
Definition stm_add_self (x : nat) : itree stmE nat :=
  c <- newTVar x ;;
  v <- readTVar c ;;
  writeTVar c (v + x) ;;
  readTVar c.

Definition io_add_self (x : nat) : itree ioE nat :=
  atomically (stm_add_self x).

(* 4) A small queue modeled as list nat inside a TVar *)

(* push at tail *)
Definition stm_enqueue (q : TVar (list nat)) (x : nat) : itree stmE unit :=
  xs <- readTVar q ;;
  writeTVar q (xs ++ [x]).

(* pop from head; retry if empty *)
Definition stm_dequeue (q : TVar (list nat)) : itree stmE nat :=
  xs <- readTVar q ;;
  match xs with
  | []      => retry
  | y :: ys => writeTVar q ys ;; Ret y
  end.

(* tryDequeue with default, using orElse to avoid blocking *)
Definition stm_tryDequeue (q : TVar (list nat)) (dflt : nat) : itree stmE nat :=
  orElse (stm_dequeue q) (Ret dflt).

(* smoke test: enqueue then dequeue must return the enqueued element *)
Definition stm_queue_roundtrip (x : nat) : itree stmE nat :=
  q <- newTVar ([] : list nat) ;;
  stm_enqueue q x ;;
  stm_dequeue q.

Definition io_queue_roundtrip (x : nat) : itree ioE nat :=
  atomically (stm_queue_roundtrip x).

(* 5) orElse + retry behavior *)
(* First branch retries on empty; second returns a constant 42 *)
Definition stm_orElse_retry_example (_ : unit) : itree stmE nat :=
  q <- newTVar ([] : list nat) ;;
  orElse (stm_dequeue q) (Ret 42).

Definition io_orElse_retry_example : itree ioE nat :=
  atomically (stm_orElse_retry_example tt).

End stmtest.

Crane Extraction "stm" stmtest.
