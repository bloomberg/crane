From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

(** Sum all values in a tree, plus an accumulator. *)
Definition sum_values (t : tree) (x : nat) : nat :=
  match t with
  | Leaf => x
  | Node l v r =>
    match l with
    | Leaf => v + x
    | Node _ lv _ =>
      match r with
      | Leaf => lv + x
      | Node _ rv _ => lv + rv + v + x
      end
    end
  end.

(** A wrapper for closures. *)
Inductive fn_box : Type :=
| Box : (nat -> nat) -> fn_box.

Definition apply_box (b : fn_box) (x : nat) : nat :=
  match b with
  | Box f => f x
  end.

(** Custom list type. *)
Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

(** ---- TEST 1: Higher-order function calling closure multiple times ----
    If f is a partial application with [&] capture and apply_twice calls
    it twice, the second call would use a moved-from value. *)
Definition apply_twice (f : nat -> nat) (x : nat) : nat := f (f x).

Definition test_hof_double : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := sum_values t in
  apply_twice f 0.
(** f(f(0)): f(0) = 60, f(60) = 120 *)

(** ---- TEST 2: Build list of closures from tree branches ----
    Each closure captures a tree value via partial application.
    The closures must survive after the function returns. *)
Fixpoint build_adders (trees : mylist tree) : mylist (nat -> nat) :=
  match trees with
  | mynil => mynil
  | mycons t rest => mycons (sum_values t) (build_adders rest)
  end.

Fixpoint apply_all (fns : mylist (nat -> nat)) (x : nat) : nat :=
  match fns with
  | mynil => 0
  | mycons f rest => f x + apply_all rest x
  end.

Definition test_closure_list : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let t3 := Node Leaf 30 Leaf in
  let fns := build_adders (mycons t1 (mycons t2 (mycons t3 mynil))) in
  apply_all fns 5.
(** 15 + 25 + 35 = 75 *)

(** ---- TEST 3: Closure in pair construction ----
    Tests whether pair/tuple construction with closures handles
    capture correctly. *)
Definition pair_of_closures (t : tree) : (nat -> nat) * (nat -> nat) :=
  (sum_values t, fun n => n).

Definition test_pair_closures : nat :=
  let t := Node Leaf 42 Leaf in
  let p := pair_of_closures t in
  fst p 10 + snd p 100.
(** 52 + 100 = 152 *)

(** ---- TEST 4: Fold composing closures ----
    Each iteration wraps the accumulator in a new closure that captures
    a tree value. Tests deep closure chaining with value type captures. *)
Fixpoint fold_compose (trees : mylist tree) (acc : nat -> nat) : nat -> nat :=
  match trees with
  | mynil => acc
  | mycons t rest => fold_compose rest (fun n => acc (sum_values t n))
  end.

Definition test_fold_compose : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let f := fold_compose (mycons t1 (mycons t2 mynil)) (fun n => n) in
  f 5.
(** 30 + 5 = 35 *)

(** ---- TEST 5: Partial application + match scrutinee reuse ----
    f captures t by partial application, then t is used as a match
    scrutinee. The escape analysis must handle this correctly. *)
Definition match_partial (t : tree) : nat :=
  let f := sum_values t in
  match t with
  | Leaf => f 0
  | Node _ v _ => f v
  end.

Definition test_match_partial : nat :=
  match_partial (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).
(** f 20 = 80 *)

(** ---- TEST 6: Deep currying chain ----
    Multi-level partial application where each level binds a new value. *)
Definition add3 (a b c : nat) : nat := a + b + c.

Definition test_deep_curry : nat :=
  let t := Node Leaf 10 Leaf in
  let v := sum_values t 0 in
  let f := add3 v in
  let g := f 20 in
  g 30.
(** 60 *)

(** ---- TEST 7: Store partial application in Box, then apply twice ----
    The Box stores a closure. If the closure uses [&] capture,
    the Box holds dangling references after make_box returns. *)
Definition make_box (t : tree) : fn_box :=
  Box (sum_values t).

Definition test_box_apply_twice : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let b := make_box t in
  apply_box b 0 + apply_box b 99.
(** 60 + 159 = 219 *)

(** ---- TEST 8: Two closures capture the same tree ----
    Both must independently own data. The second partial application
    should not move the tree. *)
Definition test_dual_capture : nat :=
  let t := Node Leaf 42 Leaf in
  let f := sum_values t in
  let g := sum_values t in
  f 1 + g 2.
(** 43 + 44 = 87 *)

(** ---- TEST 9: Map tree with closure ----
    Recursive function that passes a closure through recursive calls.
    The closure must remain valid across all recursive invocations. *)
Fixpoint map_tree (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (map_tree f l) (f v) (map_tree f r)
  end.

Definition test_map_tree : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let t2 := map_tree (fun n => n + 1) t in
  sum_values t2 0.
(** 11 + 31 + 21 + 0 = 63 *)

(** ---- TEST 10: Partial application stored in Box via match ----
    The partial application captures a match-bound tree value and
    is stored in a Box. Tests closure escape through constructor inside match. *)
Definition box_from_match (t : tree) : fn_box :=
  match t with
  | Leaf => Box (fun n => n)
  | Node l _ _ => Box (sum_values l)
  end.

Definition test_box_from_match : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let b := box_from_match t in
  apply_box b 5.
(** l = Node Leaf 10 Leaf, sum_values l 5 = 10 + 5 = 15 *)

(** ---- TEST 11: Closure captures two different tree values ----
    A function that creates a closure capturing TWO different trees.
    Both must be correctly cloned or captured by value. *)
Definition combine_trees (t1 t2 : tree) (x : nat) : nat :=
  sum_values t1 x + sum_values t2 x.

Definition test_combine : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let f := combine_trees t1 t2 in
  f 5.
(** (10+5) + (20+5) = 40 *)

(** ---- TEST 12: Chain of partial applications with intermediate let ----
    f captures t, then g uses f's result to build another closure.
    Tests that intermediate values are properly kept alive. *)
Definition test_chain_partial : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := sum_values t in
  let v := f 0 in
  let g := add3 v in
  g 100 200.
(** v = 60, g 100 200 = 60 + 100 + 200 = 360 *)

End MemSafetyProbe.

Crane Extraction "mem_safety_probe" MemSafetyProbe.
