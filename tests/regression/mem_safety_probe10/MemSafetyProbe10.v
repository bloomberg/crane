From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe10.

(** Probe 10: Recursive functions that RETURN closures.
    Tests whether return_captures_by_value processes lambdas
    correctly through loopification. *)

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

(** TEST 1: Recursive function that returns a closure.
    Each level composes the closure from recursive results.
    After loopification, these closures are assigned to _result,
    not returned via Sreturn. *)
Fixpoint tree_to_adder (t : tree) : nat -> nat :=
  match t with
  | Leaf => fun n => n
  | Node l v r =>
    let fl := tree_to_adder l in
    let fr := tree_to_adder r in
    fun n => fl (v + fr n)
  end.

Definition test_tree_adder : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let f := tree_to_adder t in
  f 5.
(** f 5 = fl (20 + fr 5) = fl (20 + (fun n => 30 + n) 5) = fl (55)
    fl = fun n => 10 + n
    fl 55 = 65 *)

(** TEST 2: Build closures during list traversal,
    where each closure captures the HEAD of the list
    and the closure from the previous step. *)
Fixpoint chain_adders (l : mylist nat) (acc : nat -> nat) : nat -> nat :=
  match l with
  | mynil => acc
  | mycons h t => chain_adders t (fun n => acc (h + n))
  end.

Definition test_chain : nat :=
  let l := mycons 10 (mycons 20 (mycons 30 mynil)) in
  let f := chain_adders l (fun x => x) in
  f 7.
(** f 7 = id(10 + (20 + (30 + 7))) = 67 *)

(** TEST 3: Recursive function returning a list of closures.
    Each closure captures the tree node's value and subtrees. *)
Fixpoint collect_adders (t : tree) : mylist (nat -> nat) :=
  match t with
  | Leaf => mynil
  | Node l v r =>
    mycons (fun n => v + n)
      (mycons (fun n => tree_sum l + n)
        (mycons (fun n => tree_sum r + n)
          (collect_adders l)))
  end.

Definition test_collect_adders : nat :=
  let t := Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf) in
  sum_fns (collect_adders t).
(** At root (10, l=Node Leaf 5 Leaf, r=Node Leaf 15 Leaf):
    f1 = fun n => 10 + n → f1 0 = 10
    f2 = fun n => tree_sum(Node Leaf 5 Leaf) + n = 5 + n → f2 0 = 5
    f3 = fun n => tree_sum(Node Leaf 15 Leaf) + n = 15 + n → f3 0 = 15
    At left (5, l=Leaf, r=Leaf):
    f4 = fun n => 5 + n → f4 0 = 5
    f5 = fun n => tree_sum Leaf + n = 0 + n → f5 0 = 0
    f6 = fun n => tree_sum Leaf + n = 0 + n → f6 0 = 0
    Total = 10 + 5 + 15 + 5 + 0 + 0 = 35 *)

(** TEST 4: Closure returned from nested match.
    Tests return_captures_by_value through Sif branches. *)
Definition choose_fn (o : option bool) (v : nat) : nat -> nat :=
  match o with
  | Some b =>
    if b then fun n => v + n
    else fun n => v * n
  | None => fun n => n
  end.

Definition test_choose : nat :=
  let f1 := choose_fn (Some true) 10 in
  let f2 := choose_fn (Some false) 3 in
  let f3 := choose_fn None 99 in
  f1 5 + f2 7 + f3 42.
(** f1 5 = 10 + 5 = 15
    f2 7 = 3 * 7 = 21
    f3 42 = 42
    Total = 78 *)

(** TEST 5: Closure capturing value from OUTER match,
    returned from INNER match. Tests nested match +
    capture interaction. *)
Definition nested_match_closure (t : tree) (b : bool) : nat -> nat :=
  match t with
  | Leaf => fun n => n
  | Node l v r =>
    match b with
    | true => fun n => tree_sum l + v + n
    | false => fun n => tree_sum r + v + n
    end
  end.

Definition test_nested : nat :=
  let t := Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf) in
  let f1 := nested_match_closure t true in
  let f2 := nested_match_closure t false in
  f1 0 + f2 0.
(** f1 0 = tree_sum(Node Leaf 5 Leaf) + 10 + 0 = 5 + 10 = 15
    f2 0 = tree_sum(Node Leaf 15 Leaf) + 10 + 0 = 15 + 10 = 25
    Total = 40 *)

(** TEST 6: Function returning closure in pair.
    Tests pair construction with closure. *)
Definition pair_with_fn (n : nat) : (nat -> nat) * nat :=
  (fun x => n + x, n * 2).

Definition test_pair_fn : nat :=
  let p := pair_with_fn 10 in
  fst p 5 + snd p.
(** fst p 5 = 10 + 5 = 15, snd p = 20, Total = 35 *)

(** TEST 7: Mutually recursive functions using a fixpoint
    where one captures the other's result as a closure. *)
Fixpoint build_tree_fns (t : tree) (depth : nat)
  : mylist (nat -> nat) :=
  match depth with
  | O => mynil
  | S d =>
    match t with
    | Leaf => mycons (fun n => n) mynil
    | Node l v r =>
      mycons (fun n => v + n)
        (mycons (fun n => tree_sum l + tree_sum r + n)
          (build_tree_fns l d))
    end
  end.

Definition test_tree_fns : nat :=
  let t := Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf) in
  sum_fns (build_tree_fns t 2).
(** depth=2, root: v=7, l=Node Leaf 3 Leaf, r=Node Leaf 11 Leaf
    f1 = fun n => 7 + n → 7
    f2 = fun n => tree_sum(Node Leaf 3 Leaf) + tree_sum(Node Leaf 11 Leaf) + n
         = 3 + 11 + n → 14
    depth=1, l=Node Leaf 3 Leaf: v=3
    f3 = fun n => 3 + n → 3
    f4 = fun n => 0 + 0 + n → 0
    Total = 7 + 14 + 3 + 0 = 24 *)

(** TEST 8: Closure returned from function, capturing a TREE value.
    The tree is a value type with unique_ptr self-references.
    Tests whether [=] capture correctly deep-copies the tree. *)
Definition make_tree_summer (t : tree) : nat -> nat :=
  fun n => tree_sum t + n.

Definition test_tree_capture : nat :=
  let t := Node (Node Leaf 100 Leaf) 200 (Node Leaf 300 Leaf) in
  let f := make_tree_summer t in
  let t2 := Node Leaf 999 Leaf in
  let _ := tree_sum t2 in
  f 0.
(** f 0 = tree_sum(Node (Node Leaf 100 Leaf) 200 (Node Leaf 300 Leaf)) + 0
    = 100 + 200 + 300 = 600 *)

End MemSafetyProbe10.

Crane Extraction "mem_safety_probe10" MemSafetyProbe10.
