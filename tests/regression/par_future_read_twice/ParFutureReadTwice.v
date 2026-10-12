(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [Monads.Par] maps a [future] to [std::future], which can be
    read once and only by its owner, while a Rocq future is an ordinary
    value.
    - Reading a future twice, [get_thread t] then [get_thread t] again,
      calls [get()] on a [std::future] the first call emptied: a member call
      on a null shared state, undefined behaviour that UndefinedBehavior
      Sanitizer, which this test is compiled with, reports.
    - Futures kept in a [list] are [const] elements, and [std::future::get]
      is not [const]: "'this' argument to member function 'get' has type
      'const std::future<unsigned long long>'".
    [std::shared_future] has the value semantics the Rocq type has. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.Std Monads.ITree Monads.Par.

Module ParFutureReadTwice.

Open Scope itree_scope.

Definition sq (n : nat) : nat := n * n.

Definition twice (n : nat) : nat :=
  runPar (t <- async sq n ;; a <- get_thread t ;; b <- get_thread t ;; Ret (a + b)).

Fixpoint spawn_all (l : list nat) : itree parE (list (future nat)) :=
  match l with [] => Ret [] | x :: t => f <- async sq x ;; fs <- spawn_all t ;; Ret (f :: fs) end.

Fixpoint join_all (l : list (future nat)) : itree parE nat :=
  match l with [] => Ret 0 | f :: t => a <- get_thread f ;; b <- join_all t ;; Ret (a + b) end.

Definition listed : nat := runPar (fs <- spawn_all [1; 2; 3] ;; join_all fs).

End ParFutureReadTwice.

Crane Extraction "par_future_read_twice" ParFutureReadTwice.
