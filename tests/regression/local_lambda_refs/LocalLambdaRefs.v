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
From Crane Require Import Mapping.NatIntStd Monads.Error Monads.ITree Monads.STMonad.
Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section S.
  Context {R : STRefs}.
  Notation E0 := (STEvent R (fun _ : nat => nat) +' exceptE Err).

  Definition bump_twice : itree E0 nat :=
    r <- newSTRef 0;;
    let fix bump (k : nat) (x : STRef nat) : itree E0 unit :=
      match k with
      | O => Ret tt
      | Datatypes.S k' => v <- readSTRef x;; writeSTRef x (v + 1);; bump k' x
      end in
    bump 3 r;;
    bump 4 r;;
    readSTRef r.

  Definition bump_each : itree E0 (nat * nat) :=
    r <- newSTRef 0;;
    s <- newSTRef 10;;
    let fix bump (k : nat) (x : STRef nat) : itree E0 unit :=
      match k with
      | O => Ret tt
      | Datatypes.S k' => v <- readSTRef x;; writeSTRef x (v + 1);; bump k' x
      end in
    bump 3 r;;
    bump 4 s;;
    a <- readSTRef r;;
    b <- readSTRef s;;
    Ret (a, b).

  Definition fill_each : itree E0 (list nat * list nat) :=
    a <- newArray 3 0;;
    b <- newArray 2 0;;
    let fix fill (i n : nat) (arr : STArray nat) : itree E0 unit :=
      match n with
      | O => Ret tt
      | Datatypes.S n' => writeArray arr i (i + 1);; fill (Datatypes.S i) n' arr
      end in
    fill 0 3 a;;
    fill 0 2 b;;
    xs <- getElems a;;
    ys <- getElems b;;
    Ret (xs, ys).
End S.

Module LocalLambdaRefs.
  Definition bump_twice : nat := run_st (@bump_twice cpp_refs).
  Definition bump_each : nat * nat := run_st (@bump_each cpp_refs).
  Definition fill_each : list nat * list nat := run_st (@fill_each cpp_refs).
  Definition nth := Eval unfold List.nth in (@List.nth nat).
End LocalLambdaRefs.

Set Crane Loopify.
Crane Extraction "local_lambda_refs" LocalLambdaRefs.
