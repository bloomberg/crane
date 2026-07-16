(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Defining a local fixpoint that calls state_bind with a result from another function
   produces a lambda that cannot be converted to the generated std::function type.
   When you simplify the call and remove state_bind, the local function is inlined and it compiles and tests successfully.
 *)

From Stdlib Require Import List Nat Bool.
From ExtLib Require Import Structures.Functor.
Import ListNotations.

Module Monadic.

(* === State monad (as function) === *)

Definition State (S A : Type) := S -> A * S.

Definition state_return {S A : Type} (x : A) : State S A :=
  fun s => (x, s).

Definition state_bind {S A B : Type} (ma : State S A) (f : A -> State S B) : State S B :=
  fun s => let '(a, s') := ma s in f a s'.


(* stub function, just returns tt *)
Definition foo_state (n : unit) : State bool unit := state_return tt.


Definition foo : bool :=
  let fix foo_state' (u : unit) : State bool unit :=
    state_bind (foo_state u) (fun _ => state_return tt)
    (* NOTE: replacing above line with `foo_state u` fixes this test *)
  in
  let '(_, a) := foo_state' tt true
  in a.


End Monadic.

Require Crane.Extraction.
From Crane Require Mapping.Std.
Crane Extraction "local_fixpoint" Monadic.foo.
