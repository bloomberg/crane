From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe14.

(** Probe 14: Stress-test closure capture safety.

    Focus on patterns where:
    1. A value type is simultaneously used in a closure AND
       consumed by another operation in the same expression
    2. Closures that capture value types are stored in
       data structures and later invoked
    3. Closures returned from helper functions that take
       value-type parameters by value (move semantics) *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint sum_fns (l : mylist (nat -> nat)) : nat :=
  match l with
  | mynil => 0
  | mycons f rest => f 0 + sum_fns rest
  end.

(** TEST 1: make_adder takes a tree by value (move).
    The closure captures tree_sum t. After the closure is created,
    t is dead in the caller, so Crane might move t.
    But the closure must hold a valid copy. *)
Definition make_adder (t : tree) : nat -> nat :=
  fun n => tree_sum t + n.

Definition use_make_adder : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := make_adder t in
  f 5.
(** tree_sum t = 60, f 5 = 60 + 5 = 65 *)

(** TEST 2: Tree used in closure AND in a let-binding.
    The let-binding forces evaluation before the closure call.
    Tests evaluation order safety. *)
Definition use_tree_twice (t : tree) : nat :=
  let ts := tree_sum t in
  let f := fun n => tree_sum t + n in
  ts + f 0.

Definition test_use_twice : nat :=
  use_tree_twice (Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf)).
(** ts = 30, f 0 = 30, Total = 60 *)

(** TEST 3: Tree used in closure, then tree passed to
    function that consumes it. The closure must not
    share state with the consumed tree. *)
Definition consume_tree (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ v _ => v
  end.

Definition closure_then_consume (t : tree) : nat :=
  let f := fun n => tree_sum t + n in
  let v := consume_tree t in
  f 0 + v.

Definition test_closure_consume : nat :=
  closure_then_consume (Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf)).
(** f 0 = 30, consume_tree t = 10, Total = 40 *)

(** TEST 4: Two closures capture same tree. Both should
    have independent copies. *)
Definition two_closures (t : tree) : nat :=
  let f1 := fun n => tree_sum t + n in
  let f2 := fun n => tree_sum t * n in
  f1 3 + f2 2.

Definition test_two_closures : nat :=
  two_closures (Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf)).
(** f1 3 = 30 + 3 = 33, f2 2 = 30 * 2 = 60, Total = 93 *)

(** TEST 5: Closure captures tree, tree is pattern-matched
    AFTER closure creation. The match destructures the tree.
    The closure must still hold the original tree. *)
Definition capture_then_match (t : tree) : nat :=
  let f := fun n => tree_sum t + n in
  match t with
  | Leaf => f 0
  | Node l v r => f v + tree_sum l + tree_sum r
  end.

Definition test_capture_match : nat :=
  capture_then_match (Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf)).
(** f = fun n => 30 + n
    match: Node case: f 10 + tree_sum(Node Leaf 5 Leaf) + tree_sum(Node Leaf 15 Leaf)
    = 40 + 5 + 15 = 60 *)

(** TEST 6: List of closures created from tree traversal.
    Each closure captures a value from its level. Closures
    are evaluated after the full traversal completes. *)
Fixpoint mylist_append {A : Type} (l1 l2 : mylist A) : mylist A :=
  match l1 with
  | mynil => l2
  | mycons x xs => mycons x (mylist_append xs l2)
  end.

Fixpoint tree_level_fns (t : tree) (depth : nat)
  : mylist (nat -> nat) :=
  match t with
  | Leaf => mynil
  | Node l v r =>
    mycons (fun n => depth * 100 + v + n)
      (mycons (fun n => tree_sum l + tree_sum r + n)
        (mylist_append (tree_level_fns l (1 + depth))
                       (tree_level_fns r (1 + depth))))
  end.

Definition test_level_fns : nat :=
  let t := Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf) in
  sum_fns (tree_level_fns t 0).
(** depth=0, v=7: f1 = fun n => 0*100 + 7 + n = 7
                  f2 = fun n => 3 + 11 + n = 14
    depth=1, v=3: f3 = fun n => 100 + 3 + n = 103
                  f4 = fun n => 0 + 0 + n = 0
    depth=1, v=11: f5 = fun n => 100 + 11 + n = 111
                   f6 = fun n => 0 + 0 + n = 0
    Total = 7 + 14 + 103 + 0 + 111 + 0 = 235 *)

(** TEST 7: Closure stored in PAIR, then extracted and called.
    Tests pair construction + closure capture interaction. *)
Definition fn_and_val (t : tree) : (nat -> nat) * nat :=
  let s := tree_sum t in
  (fun n => s + n, s).

Definition test_fn_and_val : nat :=
  let t := Node (Node Leaf 100 Leaf) 200 (Node Leaf 300 Leaf) in
  let p := fn_and_val t in
  fst p 5 + snd p.
(** s = 600, fst p 5 = 605, snd p = 600, Total = 1205 *)

(** TEST 8: Large tree stress test. Many closures, deep recursion. *)
Fixpoint make_balanced (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node (make_balanced n') n Leaf
  end.

Fixpoint collect_closures (t : tree) : mylist (nat -> nat) :=
  match t with
  | Leaf => mynil
  | Node l v r =>
    mycons (fun n => v + n)
      (mylist_append (collect_closures l) (collect_closures r))
  end.

Definition test_stress : nat :=
  let t := make_balanced 8 in
  sum_fns (collect_closures t).
(** Sum of all node values: 8+7+6+5+4+3+2+1 = 36 *)

End MemSafetyProbe14.

Crane Extraction "mem_safety_probe14" MemSafetyProbe14.
