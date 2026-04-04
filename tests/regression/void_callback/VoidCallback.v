(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Edge cases for void-returning callbacks in monadic and pure contexts. *)

From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module VoidCallback.

(** 1. Pure HOF with void callback — the callback returns unit *)
Fixpoint for_each (f : nat -> unit) (xs : list nat) : unit :=
  match xs with
  | nil => tt
  | cons x rest => let _ := f x in for_each f rest
  end.

Definition print_nat (n : nat) : unit := tt.
Definition test_for_each : unit := for_each print_nat (cons 1 (cons 2 nil)).

(** 2. Monadic for-each: callback returns itree ioE unit *)
Fixpoint for_each_m (f : nat -> itree ioE unit) (xs : list nat) : itree ioE unit :=
  match xs with
  | nil => Ret tt
  | cons x rest => f x ;; for_each_m f rest
  end.

Definition test_for_each_m : itree ioE unit :=
  for_each_m (fun n => print_endline "item") (cons 1 (cons 2 nil)).

(** 3. Pure function returning unit, used in let *)
Definition side_effect_pure (n : nat) : unit := tt.

Definition use_side_effect : nat :=
  let _ := side_effect_pure 5 in
  let _ := side_effect_pure 10 in
  42.

(** 4. Callback that ignores argument and returns nat *)
Fixpoint ignore_and_count (f : nat -> unit) (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | cons x rest => let _ := f x in S (ignore_and_count f rest)
  end.

Definition test_ignore : nat :=
  ignore_and_count print_nat (cons 1 (cons 2 (cons 3 nil))).

(** 5. Nested void callbacks *)
Definition apply_twice (f : nat -> unit) (n : nat) : unit :=
  let _ := f n in f n.

Definition test_apply_twice : unit := apply_twice print_nat 42.

(** 6. Void function as argument to polymorphic function *)
Definition apply_to {A B : Type} (f : A -> B) (x : A) : B := f x.

Definition test_apply_to_void : unit := apply_to print_nat 5.

(** 7. Void returning function in a match arm *)
Definition void_in_match (b : bool) : unit :=
  if b then print_nat 1 else print_nat 2.

(** 8. Option of void function result *)
Definition void_option (b : bool) : option unit :=
  if b then Some (print_nat 1) else None.

End VoidCallback.

Crane Extraction "void_callback" VoidCallback.
