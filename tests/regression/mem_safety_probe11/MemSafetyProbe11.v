From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module MemSafetyProbe11.

(** Probe 11: Closure escape through ACCUMULATOR in loopified
    tail-recursive functions, specifically testing the interaction
    between the new flatten optimization (make_owned_param_matches)
    and closure capture in match branches.

    Key attack vector: A tail-recursive function with an accumulator
    that stores closures. Each closure captures a unique_ptr field
    from the match destructuring. After loopification, the match
    uses v_mut() and mutable bindings. If closures capture mutable
    bindings by reference and the field is later moved, we get
    use-after-move. *)

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

Fixpoint sum_fns (l : mylist (nat -> nat)) : nat :=
  match l with
  | mynil => 0
  | mycons f rest => f 0 + sum_fns rest
  end.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

Fixpoint tree_depth (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l _ r =>
    let dl := tree_depth l in
    let dr := tree_depth r in
    1 + (if Nat.leb dl dr then dr else dl)
  end.

(** TEST 1: Accumulate closures that capture BOTH subtrees.
    Each closure uses tree_sum on both l and r.
    Both subtrees are also used in recursive calls.
    After loopification with flatten, the subtrees' unique_ptrs
    may be moved into continuation frames. *)
Fixpoint collect_dual_captures (t : tree)
  (acc : mylist (nat -> nat)) : mylist (nat -> nat) :=
  match t with
  | Leaf => acc
  | Node l v r =>
    let f := fun _n => tree_sum l + tree_sum r in
    let acc2 := mycons f acc in
    collect_dual_captures l (collect_dual_captures r acc2)
  end.

Definition test_dual_capture : nat :=
  let t := Node (Node Leaf 5 Leaf) 10
               (Node Leaf 15 (Node Leaf 20 Leaf)) in
  sum_fns (collect_dual_captures t mynil).
(** Root(10): f = tree_sum(Node Leaf 5 Leaf) + tree_sum(Node Leaf 15 (Node Leaf 20 Leaf))
              = 5 + 35 = 40
    15-node: f = tree_sum(Leaf) + tree_sum(Node Leaf 20 Leaf) = 0 + 20 = 20
    20-node: f = tree_sum(Leaf) + tree_sum(Leaf) = 0
    5-node: f = tree_sum(Leaf) + tree_sum(Leaf) = 0
    Total = 0 + 0 + 20 + 40 = 60 *)

(** TEST 2: Closure captures the TAIL of the list (unique_ptr field).
    Each closure computes length of the tail.
    After loopification, the tail pointer may be moved. *)
Fixpoint capture_tails (l : mylist nat)
  (acc : mylist (nat -> nat)) : mylist (nat -> nat) :=
  match l with
  | mynil => acc
  | mycons x xs =>
    let f := fun _n => x + length xs in
    capture_tails xs (mycons f acc)
  end.

Definition test_capture_tails : nat :=
  let l := mycons 100 (mycons 200 (mycons 300 mynil)) in
  sum_fns (capture_tails l mynil).
(** x=100, xs=[200,300]: f = 100 + 2 = 102
    x=200, xs=[300]: f = 200 + 1 = 201
    x=300, xs=[]: f = 300 + 0 = 300
    fns reversed: [f300, f200, f100]
    Total = 300 + 201 + 102 = 603 *)

(** TEST 3: Closure captures a SUBTREE, but the subtree is ALSO
    passed to a recursive call AND used in the continuation.
    Tests whether the clone/pre-copy mechanism handles triple use. *)
Fixpoint triple_use_tree (t : tree)
  (acc : mylist (nat -> nat)) : mylist (nat -> nat) :=
  match t with
  | Leaf => acc
  | Node l v r =>
    let fl := fun _n => tree_sum l in
    let fr := fun _n => tree_sum r in
    let acc2 := mycons fr (mycons fl acc) in
    triple_use_tree l (triple_use_tree r acc2)
  end.

Definition test_triple_use : nat :=
  let t := Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf) in
  sum_fns (triple_use_tree t mynil).
(** Root(7): fl = tree_sum(Node Leaf 3 Leaf) = 3
             fr = tree_sum(Node Leaf 11 Leaf) = 11
    Right(11): fl = tree_sum(Leaf) = 0
               fr = tree_sum(Leaf) = 0
    Left(3): fl = tree_sum(Leaf) = 0
             fr = tree_sum(Leaf) = 0
    fns: [fl_left=0, fr_left=0, fl_right=0, fr_right=0, fr_root=11, fl_root=3]
    Total = 0 + 0 + 0 + 0 + 11 + 3 = 14 *)

(** TEST 4: Closure capturing pattern variables from a NESTED match.
    The outer match destructs a tree, the inner match destructs a list.
    Tests pre-copy across nested match scopes. *)
Definition nested_capture (t : tree) (l : mylist nat) : nat -> nat :=
  match t with
  | Leaf => fun n => n
  | Node lt v rt =>
    match l with
    | mynil => fun n => v + n
    | mycons h _ =>
      fun n => tree_sum lt + tree_sum rt + h + v + n
    end
  end.

Definition test_nested_capture : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let l := mycons 5 (mycons 99 mynil) in
  let f := nested_capture t l in
  f 7.
(** tree_sum(Node Leaf 10 Leaf) + tree_sum(Node Leaf 30 Leaf) + 5 + 20 + 7
    = 10 + 30 + 5 + 20 + 7 = 72 *)

(** TEST 5: Tail-recursive function with two accumulators,
    one of which stores closures that capture the other.
    Tests whether accumulator values are properly captured. *)
Fixpoint dual_accum (l : mylist nat) (sum_acc : nat)
  (fn_acc : mylist (nat -> nat)) : mylist (nat -> nat) :=
  match l with
  | mynil => fn_acc
  | mycons x xs =>
    let new_sum := sum_acc + x in
    let f := fun _n => new_sum in
    dual_accum xs new_sum (mycons f fn_acc)
  end.

Definition test_dual_accum : nat :=
  let l := mycons 10 (mycons 20 (mycons 30 mynil)) in
  sum_fns (dual_accum l 0 mynil).
(** x=10: new_sum=10, f=fun _n => 10
    x=20: new_sum=30, f=fun _n => 30
    x=30: new_sum=60, f=fun _n => 60
    fns reversed: [f60, f30, f10]
    Total = 60 + 30 + 10 = 100 *)

(** TEST 6: Function that matches on a tree AND returns a closure
    that RETURNS A TREE. Tests capture of value types in returned
    closures where the return type contains unique_ptr. *)
Definition tree_transformer (t : tree) : nat -> tree :=
  match t with
  | Leaf => fun n => Node Leaf n Leaf
  | Node l v r =>
    fun n => Node l (v + n) r
  end.

Definition test_tree_transformer : nat :=
  let t := Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf) in
  let f := tree_transformer t in
  let t2 := f 100 in
  tree_sum t2.
(** f 100 = Node (Node Leaf 5 Leaf) (10 + 100) (Node Leaf 15 Leaf)
         = Node (Node Leaf 5 Leaf) 110 (Node Leaf 15 Leaf)
    tree_sum = 5 + 110 + 15 = 130 *)

End MemSafetyProbe11.

Crane Extraction "mem_safety_probe11" MemSafetyProbe11.
