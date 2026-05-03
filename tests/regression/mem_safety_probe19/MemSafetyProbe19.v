From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe19.

(** Probe 19: return_captures_by_value gap.

    Attack vector: return_captures_by_value (translation.ml:1220-1227)
    only processes top-level Sreturn statements. When a function's body
    is an Sif or Smatch (from if/match in Rocq), the outer List.map
    matches [s -> s] and passes through unchanged, leaving [&] lambdas
    inside branches unconverted to [=]. This means closures returned
    from inside if/match branches capture local variables by reference,
    creating dangling references after the function returns. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** TEST 1: Return closure from if-branch.
    The if becomes a top-level Sif in the function body.
    return_captures_by_value won't recurse into it. *)
Definition choose_fn (t : tree) (b : bool) : nat -> nat :=
  if b then fun n => tree_sum t + n
  else fun n => n.

Definition test_choose : nat :=
  let f := choose_fn (Node Leaf 42 Leaf) true in
  f 0.
(** tree_sum (Node Leaf 42 Leaf) = 42. f(0) = 42 + 0 = 42 *)

(** TEST 2: Return closure from match on option.
    The match becomes a top-level Smatch. *)
Inductive myopt (A : Type) : Type :=
| mynone : myopt A
| mysome : A -> myopt A.
Arguments mynone {A}.
Arguments mysome {A}.

Definition option_fn (t : tree) (o : myopt nat) : nat -> nat :=
  match o with
  | mysome k => fun n => tree_sum t + k + n
  | mynone => fun n => n
  end.

Definition test_option_fn : nat :=
  let f := option_fn (Node Leaf 10 Leaf) (mysome 5) in
  f 3.
(** tree_sum = 10. f(3) = 10 + 5 + 3 = 18 *)

(** TEST 3: Return closure from match on custom 3-constructor type. *)
Inductive choice : Type :=
| CLeft : choice
| CRight : choice
| CBoth : choice.

Definition choice_fn (t : tree) (c : choice) : nat -> nat :=
  match c with
  | CLeft => fun n => tree_sum t + n
  | CRight => fun n => n
  | CBoth => fun n => tree_sum t + tree_sum t + n
  end.

Definition test_choice_left : nat :=
  let f := choice_fn (Node (Node Leaf 3 Leaf) 7 Leaf) CLeft in
  f 0.
(** tree_sum = 3 + 7 = 10. f(0) = 10 *)

Definition test_choice_both : nat :=
  let f := choice_fn (Node Leaf 5 Leaf) CBoth in
  f 1.
(** tree_sum = 5. f(1) = 5 + 5 + 1 = 11 *)

(** TEST 4: Closure returned from if, capturing a locally-built tree.
    The let-bound tree is on the stack. If the returned lambda
    captures by [&], it holds a reference to the dead stack frame. *)
Definition make_adder (n : nat) (b : bool) : nat -> nat :=
  let t := Node Leaf n Leaf in
  if b then fun m => tree_sum t + m
  else fun m => m.

Definition test_make_adder : nat :=
  let f := make_adder 20 true in
  f 5.
(** tree_sum (Node Leaf 20 Leaf) = 20. f(5) = 25 *)

(** TEST 5: Double use of returned closure.
    Ensures the closure is a real std::function, not inlined. *)
Definition test_double_use : nat :=
  let f := choose_fn (Node Leaf 7 Leaf) true in
  f 1 + f 2.
(** f(1) = 7+1=8, f(2) = 7+2=9. Total = 17 *)

(** TEST 6: Pass returned closure to a higher-order function. *)
Definition apply_to (f : nat -> nat) (x : nat) : nat := f x.

Definition test_pass_closure : nat :=
  let f := choose_fn (Node Leaf 15 Leaf) true in
  apply_to f 10.
(** f(10) = 15 + 10 = 25 *)

(** TEST 7: Nested match returning closures at multiple levels. *)
Definition nested_match_fn (t : tree) (b1 b2 : bool) : nat -> nat :=
  if b1
  then (if b2
        then fun n => tree_sum t + n
        else fun n => tree_sum t + tree_sum t + n)
  else fun n => n.

Definition test_nested_match : nat :=
  let f := nested_match_fn (Node Leaf 4 Leaf) true true in
  f 0.
(** f(0) = 4 *)

Definition test_nested_match2 : nat :=
  let f := nested_match_fn (Node Leaf 4 Leaf) true false in
  f 0.
(** f(0) = 4 + 4 = 8 *)

(** TEST 8: Closure from match, used across let-bindings.
    Maximum distance between closure creation and use. *)
Definition test_delayed_use : nat :=
  let f := choice_fn (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) CLeft in
  let a := 100 in
  let b := a + 200 in
  let c := b + 300 in
  f c.
(** tree_sum = 1+2+3 = 6. c = 100+200+300 = 600. f(600) = 606 *)

End MemSafetyProbe19.

Crane Extraction "mem_safety_probe19" MemSafetyProbe19.
