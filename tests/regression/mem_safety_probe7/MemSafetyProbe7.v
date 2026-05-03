From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe7.

(** These tests FORCE closures that capture recursive self-reference
    fields (unique_ptr) by storing them in data structures.
    Closures return SCALAR values but COMPUTE from captured
    recursive structures (lists/trees). *)

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ xs => 1 + length xs
  end.

Fixpoint sum_list (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x xs => x + sum_list xs
  end.

(** TEST 1: Build a list of closures where each captures the TAIL
    and computes its length. The tail is unique_ptr. *)
Fixpoint build_len_closures (l : mylist nat) : mylist (unit -> nat) :=
  match l with
  | mynil => mynil
  | mycons _ xs =>
    mycons (fun _ => length xs) (build_len_closures xs)
  end.

Fixpoint sum_fns (l : mylist (unit -> nat)) : nat :=
  match l with
  | mynil => 0
  | mycons f rest => f tt + sum_fns rest
  end.

Definition test_len_closures : nat :=
  let l := mycons 1 (mycons 2 (mycons 3 (mycons 4 mynil))) in
  let fns := build_len_closures l in
  sum_fns fns.
(** Lengths: 3, 2, 1, 0. Sum = 6. *)

(** TEST 2: Build closures that compute the SUM of the tail.
    Each closure captures the entire tail sublist. *)
Fixpoint build_sum_closures (l : mylist nat) : mylist (unit -> nat) :=
  match l with
  | mynil => mynil
  | mycons _ xs =>
    mycons (fun _ => sum_list xs) (build_sum_closures xs)
  end.

Definition test_sum_closures : nat :=
  let l := mycons 10 (mycons 20 (mycons 30 mynil)) in
  let fns := build_sum_closures l in
  sum_fns fns.
(** Sums: sum[20,30]=50, sum[30]=30, sum[]=0. Total = 80. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** TEST 3: Build closures from tree that each capture a subtree
    and compute its sum. *)
Fixpoint tree_sum_closures (t : tree) : mylist (unit -> nat) :=
  match t with
  | Leaf => mynil
  | Node l v r =>
    mycons (fun _ => tree_sum l)
      (mycons (fun _ => tree_sum r)
        mynil)
  end.

Definition test_tree_closures : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let fns := tree_sum_closures t in
  sum_fns fns.
(** Closures: tree_sum(Node Leaf 10 Leaf)=10,
    tree_sum(Node Leaf 30 Leaf)=30. Sum = 40. *)

(** TEST 4: Each closure captures the tail AND the current value.
    After building all closures, call them — the captured lists
    must be independent copies. *)
Fixpoint build_accum_closures (l : mylist nat) : mylist (nat -> nat) :=
  match l with
  | mynil => mynil
  | mycons x xs =>
    mycons (fun n => x + sum_list xs + n) (build_accum_closures xs)
  end.

Fixpoint apply_all (l : mylist (nat -> nat)) (x : nat) : nat :=
  match l with
  | mynil => x
  | mycons f rest => f (apply_all rest x)
  end.

Definition test_accum_closures : nat :=
  let l := mycons 1 (mycons 2 (mycons 3 mynil)) in
  let fns := build_accum_closures l in
  apply_all fns 0.
(** f1: n => 1 + sum[2,3] + n = 1 + 5 + n = 6 + n
    f2: n => 2 + sum[3] + n = 2 + 3 + n = 5 + n
    f3: n => 3 + sum[] + n = 3 + 0 + n = 3 + n
    apply_all = f1(f2(f3(0))) = f1(f2(3)) = f1(8) = 14 *)

(** TEST 5: Create closures that capture BOTH children of a tree
    and use them independently. Both l and r are unique_ptr. *)
Definition make_subtree_getters (t : tree) : (unit -> nat) * (unit -> nat) :=
  match t with
  | Leaf => (fun _ => 0, fun _ => 0)
  | Node l v r => (fun _ => tree_sum l, fun _ => tree_sum r)
  end.

Definition test_subtree_getters : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let p := make_subtree_getters t in
  fst p tt + snd p tt.
(** tree_sum(left) = 10, tree_sum(right) = 30. Total = 40. *)

(** TEST 6: Stress test — large list, each closure captures
    the entire remaining tail. *)
Fixpoint make_nat_list (n : nat) : mylist nat :=
  match n with
  | O => mynil
  | S n' => mycons n (make_nat_list n')
  end.

Definition test_stress_closures : nat :=
  let l := make_nat_list 20 in
  let fns := build_len_closures l in
  sum_fns fns.
(** Lengths: 19, 18, ..., 1, 0. Sum = 19*20/2 = 190. *)

End MemSafetyProbe7.

Crane Extraction "mem_safety_probe7" MemSafetyProbe7.
