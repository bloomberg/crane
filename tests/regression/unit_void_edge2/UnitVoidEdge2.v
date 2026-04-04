(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Edge cases for unit→void extraction — round 2.
    Focuses on variable usage after unit binding. *)

From Corelib Require Import PrimString.
From Crane Require Import Mapping.NatIntStd Mapping.Std Monads.ITree Monads.IO.
From Crane Require Extraction.

Module UnitVoidEdge2.

Open Scope itree_scope.

(* === Non-monadic: let-bound unit variable used in body === *)

Definition take_unit (u : unit) : nat := 42.

(* 1. Let-bind a unit call, use the variable as argument *)
Definition opaque_unit (n : nat) : unit := tt.

Definition let_use_as_arg (n : nat) : nat :=
  let x := opaque_unit n in
  take_unit x.

(* 2. Let-bind a unit call, return the variable *)
Definition let_return_unit (n : nat) : unit :=
  let x := opaque_unit n in
  x.

(* 3. Let-bind a unit call, match on the variable *)
Definition let_match_unit (n : nat) : nat :=
  let x := opaque_unit n in
  match x with tt => n end.

(* 4. Nested let-bind-and-use *)
Definition let_chain_use (n : nat) : nat :=
  let a := opaque_unit n in
  let b := a in
  take_unit b.

(* 5. Let-bind unit, use in both branches of an if *)
Definition let_use_in_if (n : nat) (flag : bool) : nat :=
  let x := opaque_unit n in
  if flag then take_unit x else 0.

(* === Monadic: bind with unit result used in continuation === *)

(* 6. x <- print "hi" ;; Ret x
   Bind produces unit, continuation returns it *)
Definition mono_bind_return : itree ioE unit :=
  x <- print "hello" ;;
  Ret x.

(* 7. x <- print "hi" ;; y <- Ret x ;; Ret tt
   Bind produces unit, rebind it, then discard *)
Definition mono_bind_rebind : itree ioE unit :=
  x <- print "hi" ;;
  y <- Ret x ;;
  Ret tt.

(* 8. Sequence of unit binds where each depends on previous *)
Definition mono_chain : itree ioE unit :=
  x <- print "a" ;;
  y <- print "b" ;;
  Ret y.

(* 9. Unit bind result used in a match *)
Definition mono_bind_match : itree ioE nat :=
  x <- print "test" ;;
  match x with tt => Ret 42 end.

(* 10. Bind result of a non-inline function returning unit *)
Definition mono_bind_opaque : itree ioE nat :=
  x <- print "setup" ;;
  Ret 99.

(* === Fixpoints with unit === *)

(* 11. Fixpoint that counts down and returns unit *)
Fixpoint count_down_unit (n : nat) : unit :=
  match n with
  | O => tt
  | S n' => count_down_unit n'
  end.

(* 12. Fixpoint returning unit, called in let binding *)
Definition call_fixpoint : nat :=
  let _ := count_down_unit 100 in
  7.

(* 13. Fixpoint returning unit, result used *)
Definition fixpoint_result_used : nat :=
  let x := count_down_unit 50 in
  take_unit x.

(* === Higher-order with unit callbacks === *)

(* 14. Callback returning unit, called and result discarded *)
Definition call_and_discard (f : nat -> unit) (n : nat) : nat :=
  let _ := f n in
  n.

(* 15. Callback returning unit, result used *)
Definition call_and_use (f : nat -> unit) (n : nat) : nat :=
  let x := f n in
  take_unit x.

(* 16. Polymorphic apply, instantiated at unit return *)
Definition apply {A B : Type} (f : A -> B) (x : A) : B := f x.

(* apply opaque_unit 5 — disabled: MapsTo<T2,T1> where T2=Unit
   conflicts with void callback.  Known limitation with polymorphic HOFs. *)
Definition apply_take_unit : nat := apply take_unit tt.

(* === option unit patterns === *)

(* 17. Function returning option unit, using Some tt *)
Definition make_some_unit (b : bool) : option unit :=
  if b then Some tt else None.

(* 18. Matching on option unit, extracting the unit *)
Definition use_option_unit (o : option unit) : nat :=
  match o with
  | Some u => take_unit u
  | None => 0
  end.

(* 19. Composing option unit *)
Definition compose_option_unit (b1 b2 : bool) : nat :=
  let o1 := make_some_unit b1 in
  let o2 := make_some_unit b2 in
  use_option_unit o1 + use_option_unit o2.

(* === Mixed patterns === *)

(* 20. Unit value in a pair, then projected *)
Inductive pair (A B : Type) : Type := Pair : A -> B -> pair A B.
Arguments Pair {A B} _ _.

Definition make_nat_unit_pair (n : nat) : pair nat unit := Pair n tt.

Definition get_fst {A B : Type} (p : pair A B) : A :=
  match p with Pair a _ => a end.

Definition use_pair : nat :=
  let p := make_nat_unit_pair 7 in
  get_fst p.

(* === Runtime verification values === *)
Definition test_let_use := let_use_as_arg 5.
Definition test_let_match := let_match_unit 3.
Definition test_let_chain := let_chain_use 8.
Definition test_let_if_t := let_use_in_if 4 true.
Definition test_let_if_f := let_use_in_if 4 false.
Definition test_call_fix := call_fixpoint.
Definition test_fix_used := fixpoint_result_used.
Definition test_call_discard := call_and_discard opaque_unit 11.
Definition test_call_use := call_and_use opaque_unit 22.
Definition test_apply_take := apply_take_unit.
Definition test_option_use := use_option_unit (Some tt).
Definition test_compose := compose_option_unit true false.
Definition test_use_pair := use_pair.

End UnitVoidEdge2.

Crane Extraction "unit_void_edge2" UnitVoidEdge2.
