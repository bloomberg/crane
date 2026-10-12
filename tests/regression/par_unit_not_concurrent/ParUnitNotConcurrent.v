(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a unit that runs [Monads.Par] tasks is not recognised as
    concurrent, so [Set Crane SingleThreaded]'s one global block heap stays
    in force while [std::async] threads allocate and free from it at once.
    [Table.unit_is_concurrent] asks whether the unit's mappings include
    [<thread>]; [Monads.Par] includes [<future>] and spawns its threads
    through [std::async].  Four tasks building and walking trees corrupt
    the heap: UndefinedBehaviorSanitizer reports a misaligned load in
    [pool.h], and AddressSanitizer reports the corruption.  [Monads.Thread]
    is recognised (see [regression/nonatomic_rc_thread_race]). *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.Std Monads.ITree Monads.Par.

Module ParUnitNotConcurrent.

Open Scope itree_scope.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

Fixpoint sum (t : tree) : nat := match t with Leaf => 0 | Node l x r => sum l + x + sum r end.
Fixpoint mk (n : nat) : tree := match n with 0 => Leaf | S m => Node (mk m) n Leaf end.
Fixpoint mirror (t : tree) : tree := match t with Leaf => Leaf | Node l x r => Node (mirror r) x (mirror l) end.
Fixpoint churn (k : nat) (t : tree) : nat := match k with 0 => sum t | S j => churn j (mirror t) end.

Definition shared : tree := mk 2000.

Definition work (k : nat) : nat := churn k shared + sum (mk 3000).

Definition race (k : nat) : nat :=
  runPar (a <- async work k ;; b <- async work k ;; c <- async work k ;; d <- async work k ;;
          x <- get_thread a ;; y <- get_thread b ;; z <- get_thread c ;; w <- get_thread d ;;
          Ret (x + y + z + w)).

End ParUnitNotConcurrent.

Set Crane SingleThreaded.
Set Crane SharedVariant.
Set Crane Loopify.
Crane Extraction "par_unit_not_concurrent" ParUnitNotConcurrent.
