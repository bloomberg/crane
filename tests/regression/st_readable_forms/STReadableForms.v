(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The forms ST code is written in, each as it should read in C++:
    - [pair_parts]: a pair read from a reference and from an array, taken
      apart where it is read ([auto [a, _] = r;]), one part unused;
    - [fib_step]: a parallel update through reads, [a, b := b, a + b]: one
      temporary, the reads of the other used as they are;
    - [sum_with]: a function over an array passed partially applied to
      [ST.for_each_with], which takes the array by its view;
    - [count_back]: a recursion that is no tail call, whose result the
      explicit stack hands back without a move;
    - [unused_param]: a function that ignores its reference, called with
      the view its caller holds: the parameter is the read view. *)

From Stdlib Require Import Arith.PeanoNat List.
From ITree Require Import Events.Exception ITree.
From Crane Require Monads.ST.
From Crane Require Import Mapping.NatIntStd Monads.Error Monads.ITree.
Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section Pairs.
  Context {R : ST.Refs}.
  Notation E0 := (ST.Event R (fun _ : nat => prod nat nat) +' exceptE Err).

  Definition pair_parts : itree E0 nat :=
    r <- ST.new_ref (3, 4);;
    a <- ST.new_array 2 (5, 6);;
    '(x, _) <- ST.read_ref r;;
    '(_, y) <- ST.read_array a 1;;
    Ret (x + y).
End Pairs.

Section Nats.
  Context {R : ST.Refs}.
  Notation E0 := (ST.Event R (fun _ : nat => nat) +' exceptE Err).

  Definition fib_step (n : nat) : itree E0 nat :=
    a <- ST.new_ref 0;;
    b <- ST.new_ref 1;;
    let fix go (k : nat) : itree E0 unit :=
      match k with
      | O => Ret tt
      | Datatypes.S k' =>
          x <- ST.read_ref a;;
          y <- ST.read_ref b;;
          ST.write_ref a y;;
          ST.write_ref b (x + y);;
          go k'
      end in
    go n;;
    ST.read_ref a.

  Definition add_at (arr : ST.array nat) (acc i : nat) : itree E0 nat :=
    v <- ST.read_array arr i;;
    Ret (acc + v).

  Definition sum_with : itree E0 nat :=
    arr <- ST.new_array 4 3;;
    ST.write_array arr 2 10;;
    ST.for_each_with (seq 0 4) 0 (add_at arr).

  Fixpoint count_back (arr : ST.array nat) (k : nat) : itree E0 nat :=
    match k with
    | O => Ret 0
    | Datatypes.S k' =>
        r <- count_back arr k';;
        ST.write_array arr (k' mod 4) r;;
        Ret (r + k)
    end.

  Definition run_count_back : itree E0 nat :=
    arr <- ST.new_array 4 0;;
    count_back arr 5.

  Definition ignore_ref (r : ST.ref nat) (n : nat) : itree E0 nat := Ret (n + 1).

  Definition pass_view (r : ST.ref nat) : itree E0 nat :=
    ST.write_ref r 2;;
    ignore_ref r 4.

  Definition unused_param : itree E0 nat :=
    r <- ST.new_ref 0;;
    pass_view r.
End Nats.

Module STReadableForms.
  Definition pair_parts : nat := ST.run_cpp (@pair_parts ST.cpp_refs).
  Definition fib_step (n : nat) : nat := ST.run_cpp (@fib_step ST.cpp_refs n).
  Definition sum_with : nat := ST.run_cpp (@sum_with ST.cpp_refs).
  Definition count_back : nat := ST.run_cpp (@run_count_back ST.cpp_refs).
  Definition unused_param : nat := ST.run_cpp (@unused_param ST.cpp_refs).
End STReadableForms.

Set Crane Loopify.
Crane Extraction "st_readable_forms" STReadableForms.
