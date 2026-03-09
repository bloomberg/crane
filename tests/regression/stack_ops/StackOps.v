(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Stack operations: pop, push, option pairs, and capacity limiting. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module StackOps.

(* From pop_stack and stack_pop_option_pair: state with just stack *)
Record state_basic : Type := mkStateBasic {
  stack_basic : list nat
}.

(* From stack_pop_option_pair: state with stack and accumulator *)
Record state_with_acc : Type := mkStateWithAcc {
  stack_with_acc : list nat;
  acc : nat
}.

(* ===== Pop operations ===== *)

Definition pop_stack (s : state_basic) : option nat * state_basic :=
  match stack_basic s with
  | [] => (None, s)
  | x :: xs => (Some x, mkStateBasic xs)
  end.

Definition is_none (o : option nat) : bool :=
  match o with
  | None => true
  | Some _ => false
  end.

Definition option_or_zero (o : option nat) : nat :=
  match o with
  | Some n => n
  | None => 0
  end.

(* Popping empty stack yields None *)
Definition empty_is_none : bool := is_none (fst (pop_stack (mkStateBasic []))).

(* Popping nonempty stack returns the top address *)
Definition some_addr : nat := option_or_zero (fst (pop_stack (mkStateBasic [9; 8]))).

(* ===== Pop with accumulator ===== *)

Definition pop_stack_acc (s : state_with_acc) : option nat * state_with_acc :=
  match stack_with_acc s with
  | [] => (None, s)
  | a :: rest => (Some a, mkStateWithAcc rest (acc s))
  end.

Definition pop_acc_test : nat :=
  match pop_stack_acc (mkStateWithAcc [9; 8] 3) with
  | (Some a, s') => a + length (stack_with_acc s') + acc s'
  | (None, s') => acc s'
  end.

(* ===== Push operations ===== *)

Definition push_stack (s : state_basic) (addr : nat) : state_basic :=
  match stack_basic s with
  | [] => mkStateBasic [addr]
  | x :: [] => mkStateBasic [addr; x]
  | x :: y :: [] => mkStateBasic [addr; x; y]
  | x :: y :: _ => mkStateBasic [addr; x; y]
  end.

Definition top_or_zero (s : state_basic) : nat :=
  match stack_basic s with
  | [] => 0
  | x :: _ => x
  end.

(* Pushing onto empty stack yields length 1 *)
Definition empty_len : nat := length (stack_basic (push_stack (mkStateBasic []) 12)).

(* Pushing onto full stack places new address at top *)
Definition overflow_head : nat := top_or_zero (push_stack (mkStateBasic [1; 2; 3]) 9).

(* Pushing onto full stack keeps depth at 3 *)
Definition overflow_len : nat := length (stack_basic (push_stack (mkStateBasic [1; 2; 3]) 9)).

(* ===== Push with capacity cap ===== *)

Definition push_stack_cap (s : state_basic) (addr : nat) : state_basic :=
  let new_stack :=
    match stack_basic s with
    | [] => [addr]
    | [a] => [addr; a]
    | [a; b] => [addr; a; b]
    | a :: b :: c :: _ => [addr; a; b]
    end in
  mkStateBasic new_stack.

Definition push_cap_test : nat :=
  length (stack_basic (push_stack_cap (mkStateBasic [10; 20; 30; 40]) 7)).

(* ===== Combined test output ===== *)

Definition t : (nat * bool) * nat * (nat * nat * nat) * nat :=
  ((some_addr, empty_is_none),
   pop_acc_test,
   (empty_len, overflow_head, overflow_len),
   push_cap_test).

End StackOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "stack_ops" StackOps.
