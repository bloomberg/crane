(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: an STM [TVar] holding a function does not compile.
    [Monads.STM] maps [newTVar] and [writeTVar] to [stm::newTVar(%a0)] and
    [stm::writeTVar(%a0, %a1)], which deduce the variable's element type
    from the value; a function value is a lambda, so [newTVar (fun x => x)]
    makes a [TVar<(lambda)>] where the program's type is
    [TVar<crane::fn<uint64_t(uint64_t)>>] -- "no viable conversion" -- and
    [writeTVar] of a lambda into a [TVar<crane::fn<...>>] finds no
    overload. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO Monads.STM.

Module StmTvarOfFunction.

Open Scope itree_scope.

Definition fntv : itree stmE nat := a <- newTVar (fun x : nat => x) ;; f <- readTVar a ;; Ret (f 1).
Definition created : itree ioE nat := atomically fntv.

Definition fnw : itree stmE nat :=
  a <- newTVar S ;; writeTVar a (fun x => x + 2) ;; f <- readTVar a ;; Ret (f 1).
Definition written : itree ioE nat := atomically fnw.

End StmTvarOfFunction.

Crane Extraction "stm_tvar_of_function" StmTvarOfFunction.
