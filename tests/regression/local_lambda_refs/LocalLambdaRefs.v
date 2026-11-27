(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** References and arrays passed to a local loop helper that is called more
    than once, so that it cannot be inlined into its caller:
    - [bump_twice] passes the same reference to every call: the helper
      captures it by reference instead of taking it, and the reference is a
      local of [bump_twice];
    - [bump_each] passes two references: the helper takes each by its view,
      [uint64_t*], and both are locals of [bump_each];
    - [fill_each] does the same with arrays, taken by [std::span]. *)

From Stdlib Require Import Arith.PeanoNat List.
From ITree Require Import Events.Exception ITree.
From Crane Require Monads.ST.
From Crane Require Import Mapping.NatIntStd Monads.Error Monads.ITree.
Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section S.
  Context {R : ST.Refs}.
  Notation E0 := (ST.Event R (fun _ : nat => nat) +' exceptE Err).

  Definition bump_twice : itree E0 nat :=
    r <- ST.new_ref 0;;
    let fix bump (k : nat) (x : ST.ref nat) : itree E0 unit :=
      match k with
      | O => Ret tt
      | Datatypes.S k' => v <- ST.read_ref x;; ST.write_ref x (v + 1);; bump k' x
      end in
    bump 3 r;;
    bump 4 r;;
    ST.read_ref r.

  Definition bump_each : itree E0 (nat * nat) :=
    r <- ST.new_ref 0;;
    s <- ST.new_ref 10;;
    let fix bump (k : nat) (x : ST.ref nat) : itree E0 unit :=
      match k with
      | O => Ret tt
      | Datatypes.S k' => v <- ST.read_ref x;; ST.write_ref x (v + 1);; bump k' x
      end in
    bump 3 r;;
    bump 4 s;;
    a <- ST.read_ref r;;
    b <- ST.read_ref s;;
    Ret (a, b).

  Definition fill_each : itree E0 (list nat * list nat) :=
    a <- ST.new_array 3 0;;
    b <- ST.new_array 2 0;;
    let fix fill (i n : nat) (arr : ST.array nat) : itree E0 unit :=
      match n with
      | O => Ret tt
      | Datatypes.S n' => ST.write_array arr i (i + 1);; fill (Datatypes.S i) n' arr
      end in
    fill 0 3 a;;
    fill 0 2 b;;
    xs <- ST.array_to_list a;;
    ys <- ST.array_to_list b;;
    Ret (xs, ys).
End S.

Module LocalLambdaRefs.
  Definition bump_twice : nat := ST.run_cpp (@bump_twice ST.cpp_refs).
  Definition bump_each : nat * nat := ST.run_cpp (@bump_each ST.cpp_refs).
  Definition fill_each : list nat * list nat := ST.run_cpp (@fill_each ST.cpp_refs).
  Definition nth := Eval unfold List.nth in (@List.nth nat).
End LocalLambdaRefs.

Set Crane Loopify.
Crane Extraction "local_lambda_refs" LocalLambdaRefs.
