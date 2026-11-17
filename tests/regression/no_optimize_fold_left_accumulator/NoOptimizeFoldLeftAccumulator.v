(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: with [Unset Crane Extraction Optimize] -- exactly, with the
    [opt_fix_fun] bit of [Crane Extraction Flag] cleared -- any [fold_left]
    whose accumulator type differs from the list's element type fails to
    compile.  The standard [fold_left] then stays a lambda around a local
    fixpoint, is turned into a method of [List], and its accumulator is
    declared at the list's own element type, [const A &x1_], instead of a
    type parameter of its own: "no matching member function for call to
    'fold_left'".  A user-written copy is not methodified and compiles. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module NoOptimizeFoldLeftAccumulator.

Definition rev' (l : list nat) : list nat := fold_left (fun acc x => x :: acc) l [].

Definition result : nat := List.length (rev' [1; 2; 3]).

End NoOptimizeFoldLeftAccumulator.

Unset Crane Extraction Optimize.
Crane Extraction "no_optimize_fold_left_accumulator" NoOptimizeFoldLeftAccumulator.
