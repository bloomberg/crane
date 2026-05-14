From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe16.

(** Probe 16: Focused on finding RUNTIME memory safety bugs.

    Attack vectors:
    1. Higher-order functions that STORE closures in data structures
       then invoke them after the original scope ends
    2. Partial application chains where each link captures a value
       that may have been moved
    3. Functions that return closures from match branches where
       the closure captures match bindings from an OWNED match
    4. fold/map patterns that build closure lists *)

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

Fixpoint myapp {A : Type} (l1 l2 : mylist A) : mylist A :=
  match l1 with
  | mynil => l2
  | mycons x xs => mycons x (myapp xs l2)
  end.

Fixpoint sum_list (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x xs => x + sum_list xs
  end.

Fixpoint length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ xs => 1 + length xs
  end.

(** TEST 1: Store a closure derived from a tree in a list,
    then invoke it after the tree goes out of scope.
    The closure should capture by value. *)
Definition make_summer (t : tree) : nat -> nat :=
  fun n => tree_sum t + n.

Fixpoint build_summers (trees : mylist tree) : mylist (nat -> nat) :=
  match trees with
  | mynil => mynil
  | mycons t rest => mycons (make_summer t) (build_summers rest)
  end.

Fixpoint apply_fns (fns : mylist (nat -> nat)) (x : nat) : nat :=
  match fns with
  | mynil => 0
  | mycons f rest => f x + apply_fns rest x
  end.

Definition test_store_closures : nat :=
  let trees := mycons (Node Leaf 10 Leaf)
    (mycons (Node Leaf 20 Leaf)
      (mycons (Node Leaf 30 Leaf) mynil)) in
  let fns := build_summers trees in
  apply_fns fns 0.
(** tree_sum of each: 10, 20, 30. Each fn adds 0. Total = 60. *)

(** TEST 2: Fold that accumulates a function by composing closures.
    Each step captures the tree from the current list element. *)
Fixpoint compose_summers (trees : mylist tree) (acc : nat -> nat) : nat -> nat :=
  match trees with
  | mynil => acc
  | mycons t rest =>
    compose_summers rest (fun n => acc (tree_sum t + n))
  end.

Definition test_compose : nat :=
  let trees := mycons (Node Leaf 5 Leaf)
    (mycons (Node Leaf 10 Leaf)
      (mycons (Node Leaf 15 Leaf) mynil)) in
  let f := compose_summers trees (fun n => n) in
  f 0.
(** (((0 + 15) + 10) + 5) = 30. *)

(** TEST 3: Build a list of closures where each closure captures
    the SAME tree at different levels.
    Tests whether the tree is properly cloned for each closure. *)
Fixpoint multi_capture_tree (t : tree) (n : nat) : mylist (nat -> nat) :=
  match n with
  | O => mynil
  | S n' => mycons (fun x => tree_sum t + x + n) (multi_capture_tree t n')
  end.

Definition test_multi_capture : nat :=
  let t := Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf) in
  let fns := multi_capture_tree t 3 in
  apply_fns fns 0.
(** tree_sum t = 21.
    fn at n=3: 21 + 0 + 3 = 24
    fn at n=2: 21 + 0 + 2 = 23
    fn at n=1: 21 + 0 + 1 = 22
    Total = 24 + 23 + 22 = 69 *)

(** TEST 4: Return a closure from inside a NESTED match.
    The closure captures bindings from BOTH match levels. *)
Definition nested_match_closure (t : tree) (l : mylist nat) : nat -> nat :=
  match t with
  | Leaf => fun n => n
  | Node lt v rt =>
    match l with
    | mynil => fun n => v + n
    | mycons x xs => fun n => tree_sum lt + tree_sum rt + v + x + n
    end
  end.

Definition test_nested_match : nat :=
  let t := Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf) in
  let l := mycons 7 (mycons 99 mynil) in
  let f := nested_match_closure t l in
  f 3.
(** tree_sum lt = 5, tree_sum rt = 15, v = 10, x = 7, n = 3.
    Result = 5 + 15 + 10 + 7 + 3 = 40 *)

(** TEST 5: A function that takes TWO trees and returns a closure
    capturing both. Tests double ownership. *)
Definition pair_closure (t1 t2 : tree) : nat -> nat :=
  fun n => tree_sum t1 + tree_sum t2 + n.

Definition test_pair_closure : nat :=
  let t1 := Node Leaf 100 Leaf in
  let t2 := Node (Node Leaf 50 Leaf) 25 Leaf in
  let f := pair_closure t1 t2 in
  f 0 + f 0.
(** tree_sum t1 = 100, tree_sum t2 = 75.
    f 0 = 175. f 0 + f 0 = 350. *)

(** TEST 6: Non-recursive closure from a deeply nested match. *)
Definition deep_nested_closure (t : tree) : nat -> nat :=
  match t with
  | Leaf => fun n => n
  | Node l v r =>
    match l with
    | Leaf => fun n => v + tree_sum r + n
    | Node ll lv lr =>
      match r with
      | Leaf => fun n => tree_sum ll + lv + tree_sum lr + v + n
      | Node rl rv rr =>
        fun n => tree_sum ll + lv + tree_sum lr + v +
                 tree_sum rl + rv + tree_sum rr + n
      end
    end
  end.

Definition test_deep_nested : nat :=
  let t := Node
    (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))
    10
    (Node (Node Leaf 4 Leaf) 5 (Node Leaf 6 Leaf)) in
  deep_nested_closure t 0.
(** ll=Node(Leaf,1,Leaf) lv=2 lr=Node(Leaf,3,Leaf)
    rl=Node(Leaf,4,Leaf) rv=5 rr=Node(Leaf,6,Leaf)
    v=10
    tree_sum ll=1, lv=2, tree_sum lr=3, v=10,
    tree_sum rl=4, rv=5, tree_sum rr=6, n=0
    Total = 1+2+3+10+4+5+6+0 = 31 *)

(** TEST 7: Map + apply pattern: build closures from tree children,
    apply them to values from another list. *)
Fixpoint zip_apply (fns : mylist (nat -> nat)) (vals : mylist nat) : mylist nat :=
  match fns with
  | mynil => mynil
  | mycons f rest_fns =>
    match vals with
    | mynil => mynil
    | mycons v rest_vals => mycons (f v) (zip_apply rest_fns rest_vals)
    end
  end.

Definition test_zip_apply : nat :=
  let trees := mycons (Node Leaf 10 Leaf)
    (mycons (Node Leaf 20 Leaf) mynil) in
  let fns := build_summers trees in
  let vals := mycons 1 (mycons 2 mynil) in
  let results := zip_apply fns vals in
  sum_list results.
(** fn1 = fun n => 10 + n, fn2 = fun n => 20 + n
    results = [fn1 1, fn2 2] = [11, 22]
    sum = 33 *)

(** TEST 8: Higher-order map: apply a function to each element
    of a tree, building a new tree of closures. *)
Fixpoint tree_map_val (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (tree_map_val l) (v + 1) (tree_map_val r)
  end.

Definition test_tree_map : nat :=
  let t := Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf) in
  tree_sum (tree_map_val t).
(** [2, 3, 4]. Sum = 9 *)

(** TEST 9: CPS-style flattening where each step builds a continuation
    that captures tree structure. *)
Fixpoint flatten_cps_aux (t : tree) (k : mylist nat -> mylist nat) : mylist nat :=
  match t with
  | Leaf => k mynil
  | Node l v r =>
    flatten_cps_aux l (fun ll =>
      flatten_cps_aux r (fun rl =>
        k (myapp ll (mycons v rl))))
  end.

Definition flatten_cps (t : tree) : mylist nat := flatten_cps_aux t (fun x => x).

Definition test_flatten_cps : nat :=
  let t := Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf) in
  sum_list (flatten_cps t).
(** Inorder: [1, 2, 3]. Sum = 6 *)

End MemSafetyProbe16.

Crane Extraction "mem_safety_probe16" MemSafetyProbe16.
