(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Monadic code — bind/return, Option/State monads. *)

From Stdlib Require Import List Nat Bool.
From ExtLib Require Import Structures.Functor.
Import ListNotations.

Module Monadic.

(* === Option monad === *)

Definition option_return {A : Type} (x : A) : option A := Some x.

Definition option_bind {A B : Type} (ma : option A) (f : A -> option B) : option B :=
  match ma with
  | None => None
  | Some a => f a
  end.

Definition safe_div (n m : nat) : option nat :=
  match m with
  | 0 => None
  | S m' => Some (n / S m')
  end.

Definition safe_sub (n m : nat) : option nat :=
  if n <? m then None else Some (n - m).

(* Chained bind — pipeline of partial operations *)
Definition div_then_sub (a b c : nat) : option nat :=
  option_bind (safe_div a b) (fun x =>
  option_bind (safe_sub x c) (fun y =>
  option_return y)).

(* === State monad (as function) === *)

Definition State (S A : Type) := S -> A * S.

Definition state_return {S A : Type} (x : A) : State S A :=
  fun s => (x, s).

Definition state_bind {S A B : Type} (ma : State S A) (f : A -> State S B) : State S B :=
  fun s => let '(a, s') := ma s in f a s'.

Definition state_get {S : Type} : State S S :=
  fun s => (s, s).

Definition state_put {S : Type} (s : S) : State S unit :=
  fun _ => (tt, s).

(* Count elements in a list using state *)
Definition count_elements {A : Type} (l : list A) : State nat nat :=
  List.fold_left
    (fun acc _ => state_bind acc (fun _ =>
      state_bind state_get (fun n =>
      state_bind (state_put (S n)) (fun _ =>
      state_return n))))
    l (state_return 0).



(* rewritten version of stateful version from here, https://wiki.haskell.org/The_Fibonacci_sequence *)
Definition fib_state (n : nat) : State (nat * nat) unit :=
  List.fold_left
    (fun acc _ => state_bind acc (fun _ =>
      state_bind state_get (fun '(a, b) =>
      state_put (b, a + b))))
    (seq 0 n)
    (state_return tt)
.


Definition fib (n : nat) : nat :=
  if n <=? 2
  then n
  else
    let '(_, (a, _)) := (fib_state n (0, 1))
    in a.

(* === Test values === *)

Definition test_return : option nat := option_return 42.
Definition test_bind_some : option nat := option_bind (Some 10) (fun x => Some (x + 1)).
Definition test_bind_none : option nat := option_bind (@None nat) (fun x => Some (x + 1)).
Definition test_safe_div_ok : option nat := safe_div 10 3.
Definition test_safe_div_zero : option nat := safe_div 10 0.
Definition test_chain_ok : option nat := div_then_sub 20 4 2.
Definition test_chain_fail : option nat := div_then_sub 20 0 2.
Definition test_state : nat * nat := count_elements [1; 2; 3; 4; 5] 0.
Definition test_state_fib : nat := fib 5.

End Monadic.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "monadic" Monadic.
