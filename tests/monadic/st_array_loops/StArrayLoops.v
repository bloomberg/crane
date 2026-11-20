(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Loopified helpers taking ST array views (docs/typed-mappings-design.md
    12.5, 24.6): with [Crane Loopify], a tail-recursive write loop becomes a
    [while] loop over its writable view [std::span<T>], and a
    non-tail-recursive read an explicit stack whose frames hold the read
    view [std::span<const T>]. *)

From Stdlib Require Import Arith.PeanoNat List.
From Corelib Require PrimString.
From ITree Require Import Events.Exception ITree.
From Crane Require Import
  Mapping.NatIntStd
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.STMonad.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Module StArrayLoops.

  Notation NatE := (STEvent nat unit (fun _ : nat => nat) +' exceptE Err).
  Notation NatArray := (STArray nat unit nat).

  Fixpoint zero_from (arr : NatArray) (i n : nat) : itree NatE unit :=
    match n with
    | O => Ret tt
    | S m => writeArray (idx := 0) arr i 0;; zero_from arr (S i) m
    end.

  Fixpoint sum_from (arr : NatArray) (i n : nat) : itree NatE nat :=
    match n with
    | O => Ret 0
    | S m =>
        x <- readArray (idx := 0) arr i;;
        r <- sum_from arr (S i) m;;
        Ret (x + r)
    end.

  Axiom run_nat : forall (A : Type), itree NatE A -> A.

  Definition loops_list (n : nat) : nat * list nat :=
    run_nat (nat * list nat)
      (arr <- newArray 0 0 (n - 1) 2;;
       zero_from arr 1 2;;
       s <- sum_from arr 0 n;;
       elems <- getElems (idx := 0) arr;;
       Ret (s, elems)).

End StArrayLoops.

Set Crane Loopify.
Crane Extract Inlined Constant StArrayLoops.run_nat => "%a0".
Crane Extraction "st_array_loops" StArrayLoops.
