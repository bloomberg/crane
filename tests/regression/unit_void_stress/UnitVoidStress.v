(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Adversarial stress test for unit→void and std::monostate extraction. *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module UnitVoidStress.

(* === A non-inlinable void-returning function (recursive) === *)
Fixpoint consume (n : nat) : unit :=
  match n with
  | O => tt
  | S m => consume m
  end.

(* A simple non-recursive void-returning function *)
Definition discard (n : nat) : unit := tt.

(* === CATEGORY 1: void call result used in expression context === *)

(* 1a. Void call result in a pair *)
Definition pair_with_void_call (n : nat) : nat * unit :=
  (42, consume n).

(* 1b. Void call result in option *)
Definition some_void_call (n : nat) : option unit :=
  Some (consume n).

(* 1c. Void call result in list *)
Definition list_void_calls : list unit :=
  cons (consume 1) (cons (consume 2) nil).

(* 1d. Void call result passed to a polymorphic function *)
Definition id_void_call (n : nat) : unit :=
  let x := consume n in x.

(* 1e. Non-recursive void call in pair *)
Definition pair_with_discard (n : nat) : nat * unit :=
  (n, discard n).

(* === CATEGORY 2: void function as first-class value === *)

(* 2a. Storing a void function and calling it *)
Definition store_and_call (n : nat) : unit :=
  let f := consume in
  f n.

(* 2b. Void function in a let, result used in pair *)
Definition pair_via_let (n : nat) : nat * unit :=
  let u := consume n in
  (42, u).

(* 2c. Conditional returning unit (both branches void) *)
Definition cond_void (b : bool) (n : nat) : unit :=
  if b then consume n else discard n.

(* 2d. Match on nat returning unit *)
Definition match_nat_void (n : nat) : unit :=
  match n with
  | O => tt
  | S m => consume m
  end.

(* === CATEGORY 3: mixing void and value in complex expressions === *)

(* 3a. Nested pairs with void *)
Definition nested_pair_void (n : nat) : (nat * unit) * nat :=
  ((n, consume n), 42).

(* 3b. Option of pair with void *)
Definition option_pair_void (n : nat) : option (nat * unit) :=
  Some (n, consume n).

(* 3c. Let-bind void, then use in pair *)
Definition let_void_then_pair (n : nat) : nat * nat :=
  let _ := consume n in
  (n, 42).

(* 3d. Sequential voids then return value *)
Definition seq_voids_value (n : nat) : nat :=
  let _ := consume n in
  let _ := consume (S n) in
  42.

(* 3e. Void in if branch, value in other *)
Definition void_in_one_branch (b : bool) (n : nat) : nat :=
  if b then
    let _ := consume n in 42
  else
    n.

(* === CATEGORY 4: callbacks and higher-order === *)

(* 4a. Map a void function over a list (callback type) *)
Fixpoint map_void {A : Type} (f : A -> unit) (l : list A) : list unit :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map_void f xs)
  end.

Definition test_map_void : list unit :=
  map_void discard (cons 1 (cons 2 nil)).

(* 4b. Apply void function, return result in option *)
Definition apply_void_to_option (f : nat -> unit) (n : nat) : option unit :=
  Some (f n).

Definition test_apply_void_option : option unit :=
  apply_void_to_option discard 42.

(* === CATEGORY 5: unit in complex return types === *)

(* 5a. Function returning option unit (NOT void-ified) *)
Definition make_some_tt : option unit := Some tt.

(* 5b. Function returning list unit *)
Definition make_unit_list : list unit := cons tt (cons tt nil).

(* 5c. Function returning pair unit unit *)
Definition make_unit_pair : unit * unit := (tt, tt).

(* === CATEGORY 6: polymorphic HOF with unit specialization === *)

(* 6a. Polymorphic apply: return type is type variable, instantiated with unit.
   When A=unit, the body `f n` calls a void-returning function but the return
   type of apply_result is a type variable, NOT void. The adapter wrapping
   ensures `f` returns std::monostate inside the template body. *)
Definition apply_result {A : Type} (f : nat -> A) (n : nat) : A := f n.

Definition test_apply_result_void : unit := apply_result consume 5.

(* 6b. Polymorphic apply where result is used in a pair *)
Definition apply_in_pair {A : Type} (f : nat -> A) (n : nat) : nat * A :=
  (n, f n).

Definition test_apply_in_pair_void : nat * unit := apply_in_pair consume 5.

(* === CATEGORY 7: mutual recursion returning unit === *)

(* 7a. Mutual fixpoint where both functions return void *)
Fixpoint even_void (n : nat) : unit :=
  match n with
  | O => tt
  | S m => odd_void m
  end
with odd_void (n : nat) : unit :=
  match n with
  | O => tt
  | S m => even_void m
  end.

Definition test_mutual_void : unit := even_void 10.

(* === CATEGORY 8: match on option in void function === *)

(* 8a. Match on option, both branches return void *)
Definition match_opt_void (o : option nat) : unit :=
  match o with
  | Some n => consume n
  | None => tt
  end.

Definition test_match_opt_void : unit := match_opt_void (Some 3).

(* === Test values === *)
Definition test_pair_void := pair_with_void_call 5.
Definition test_some_void := some_void_call 3.
Definition test_let_void := let_void_then_pair 7.
Definition test_seq := seq_voids_value 10.
Definition test_branch := void_in_one_branch true 5.

End UnitVoidStress.

Crane Extraction "unit_void_stress" UnitVoidStress.
