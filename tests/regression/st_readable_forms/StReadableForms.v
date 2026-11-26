(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The forms ST code is written in, each as it should read in C++:
    - [pair_parts]: a pair read from a reference and from an array, taken
      apart where it is read ([auto [a, _] = r;]), one part unused;
    - [fib_step]: a parallel update through reads, [a, b := b, a + b]: one
      temporary, the reads of the other used as they are;
    - [sum_with]: a function over an array passed partially applied to
      [for_each_with], which takes the array by its view;
    - [count_back]: a recursion that is no tail call, whose result the
      explicit stack hands back without a move;
    - [unused_param]: a function that ignores its reference, called with
      the view its caller holds: the parameter is the read view. *)

From Stdlib Require Import Arith.PeanoNat List.
From ITree Require Import Events.Exception ITree.
From Crane Require Import Mapping.NatIntStd Monads.Error Monads.ITree Monads.STMonad.
Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section Pairs.
  Context {R : STRefs}.
  Notation E0 := (STEvent R (fun _ : nat => prod nat nat) +' exceptE Err).

  Definition pair_parts : itree E0 nat :=
    r <- newSTRef (3, 4);;
    a <- newArray 2 (5, 6);;
    '(x, _) <- readSTRef r;;
    '(_, y) <- readArray a 1;;
    Ret (x + y).
End Pairs.

Section Nats.
  Context {R : STRefs}.
  Notation E0 := (STEvent R (fun _ : nat => nat) +' exceptE Err).

  Definition fib_step (n : nat) : itree E0 nat :=
    a <- newSTRef 0;;
    b <- newSTRef 1;;
    let fix go (k : nat) : itree E0 unit :=
      match k with
      | O => Ret tt
      | Datatypes.S k' =>
          x <- readSTRef a;;
          y <- readSTRef b;;
          writeSTRef a y;;
          writeSTRef b (x + y);;
          go k'
      end in
    go n;;
    readSTRef a.

  Definition add_at (arr : STArray nat) (acc i : nat) : itree E0 nat :=
    v <- readArray arr i;;
    Ret (acc + v).

  Definition sum_with : itree E0 nat :=
    arr <- newArray 4 3;;
    writeArray arr 2 10;;
    for_each_with (seq 0 4) 0 (add_at arr).

  Fixpoint count_back (arr : STArray nat) (k : nat) : itree E0 nat :=
    match k with
    | O => Ret 0
    | Datatypes.S k' =>
        r <- count_back arr k';;
        writeArray arr (k' mod 4) r;;
        Ret (r + k)
    end.

  Definition run_count_back : itree E0 nat :=
    arr <- newArray 4 0;;
    count_back arr 5.

  Definition ignore_ref (r : STRef nat) (n : nat) : itree E0 nat := Ret (n + 1).

  Definition pass_view (r : STRef nat) : itree E0 nat :=
    writeSTRef r 2;;
    ignore_ref r 4.

  Definition unused_param : itree E0 nat :=
    r <- newSTRef 0;;
    pass_view r.
End Nats.

Module StReadableForms.
  Definition pair_parts : nat := run_st (@pair_parts cpp_refs).
  Definition fib_step (n : nat) : nat := run_st (@fib_step cpp_refs n).
  Definition sum_with : nat := run_st (@sum_with cpp_refs).
  Definition count_back : nat := run_st (@run_count_back cpp_refs).
  Definition unused_param : nat := run_st (@unused_param cpp_refs).
End StReadableForms.

Set Crane Loopify.
Crane Extraction "st_readable_forms" StReadableForms.
