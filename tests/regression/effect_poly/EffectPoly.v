(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Edge cases for polymorphic functions over effects and itrees. *)

From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module EffectPoly.

(** 1. Polymorphic monadic map *)
Definition map_result {A B : Type} (f : A -> B) (m : itree ioE A) : itree ioE B :=
  a <- m ;; Ret (f a).

Definition test_map_result : itree ioE nat :=
  map_result S (Ret 41).

(** 2. Polymorphic bind-and-return *)
Definition lift_pure {A : Type} (x : A) : itree ioE A := Ret x.

Definition test_lift_nat : itree ioE nat := lift_pure 42.
Definition test_lift_string : itree ioE string := lift_pure "hello".
Definition test_lift_bool : itree ioE bool := lift_pure true.

(** 3. Monadic when / guard *)
Definition when_ (b : bool) (action : itree ioE unit) : itree ioE unit :=
  if b then action else Ret tt.

Definition test_when : itree ioE unit :=
  when_ true (print_endline "guarded").

(** 4. Monadic unless *)
Definition unless (b : bool) (action : itree ioE unit) : itree ioE unit :=
  if b then Ret tt else action.

Definition test_unless : itree ioE unit :=
  unless false (print_endline "unguarded").

(** 5. Monadic sequence of list of actions *)
Fixpoint sequence_void (actions : list (itree ioE unit)) : itree ioE unit :=
  match actions with
  | nil => Ret tt
  | cons a rest => a ;; sequence_void rest
  end.

Definition test_sequence_void : itree ioE unit :=
  sequence_void (cons (print_endline "a") (cons (print_endline "b") nil)).

(** 6. Polymorphic fold over itree results *)
Fixpoint fold_m {A B : Type} (f : A -> B -> itree ioE A) (init : A) (xs : list B) : itree ioE A :=
  match xs with
  | nil => Ret init
  | cons x rest =>
    acc <- f init x ;;
    fold_m f acc rest
  end.

Definition sum_with_logging (acc n : nat) : itree ioE nat :=
  print_endline "adding" ;;
  Ret (acc + n).

Definition test_fold : itree ioE nat :=
  fold_m sum_with_logging 0 (cons 1 (cons 2 (cons 3 nil))).

(** 7. Returning a pair from a monadic computation *)
Definition read_two_lines : itree ioE (string * string) :=
  a <- get_line ;;
  b <- get_line ;;
  Ret (a, b).

(** 8. Chaining monadic functions with different return types *)
Definition chain_types : itree ioE int :=
  print_endline "enter a number:" ;;
  line <- get_line ;;
  let len := PrimString.length line in
  Ret len.

End EffectPoly.

Crane Extraction "effect_poly" EffectPoly.
