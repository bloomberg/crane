(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Loopified helpers taking ST array views: with [Crane Loopify], a
    tail-recursive write loop becomes a [while] loop over its writable view
    [std::span<T>], and a non-tail-recursive read an explicit stack whose
    frames hold the read view [std::span<const T>]. *)

From Stdlib Require Import Arith.PeanoNat List.
From Corelib Require PrimString.
From ITree Require Import Events.Exception ITree.
From Crane Require Monads.ST.
From Crane Require Import
  Mapping.NatInt
  Monads.Error
  Monads.ITree.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Module STArrayLoops.

  Notation NatE := (ST.Event ST.cpp_refs (fun _ : nat => nat) +' exceptE Err).
  Notation NatArray := (@ST.array ST.cpp_refs nat).

  Fixpoint zero_from (arr : NatArray) (i n : nat) : itree NatE unit :=
    match n with
    | O => Ret tt
    | S m => ST.write_array arr i 0;; zero_from arr (S i) m
    end.

  Fixpoint sum_from (arr : NatArray) (i n : nat) : itree NatE nat :=
    match n with
    | O => Ret 0
    | S m =>
        x <- ST.read_array arr i;;
        r <- sum_from arr (S i) m;;
        Ret (x + r)
    end.

  Definition loops_list (n : nat) : nat * list nat :=
    ST.run_cpp
      (arr <- ST.new_array n 2;;
       zero_from arr 1 2;;
       s <- sum_from arr 0 n;;
       elems <- ST.array_to_list arr;;
       Ret (s, elems)).

End STArrayLoops.

Set Crane Loopify.
Crane Extraction "st_array_loops" STArrayLoops.
