From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe6.

(** These tests probe closures that capture RECURSIVE self-reference
    fields from match bindings. In C++, these fields are unique_ptr.
    A lambda capturing a unique_ptr by [=] fails (non-copyable).
    A lambda capturing by [&] would dangle if returned.
    Crane must pre-copy or clone the field.

    NOTE: All functions use nat as FIRST argument to avoid
    methodification bugs with curried return types. *)

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

(** TEST 1: Return a closure that uses the TAIL of the list.
    xs is a unique_ptr<mylist> field — the closure must clone it. *)
Definition tail_adder {A : Type} (dummy : nat) (l : mylist A) : nat -> nat :=
  match l with
  | mynil => fun n => n
  | mycons _ xs => fun n => length xs + n
  end.

Definition test_tail_adder : nat :=
  let l := mycons 1 (mycons 2 (mycons 3 mynil)) in
  let f := tail_adder 0 l in
  f 100.
(** xs = [2,3], length xs = 2. f 100 = 2 + 100 = 102 *)

(** TEST 2: Closure from match that reconstructs using both
    a value field and a recursive field. *)
Definition head_and_tail {A : Type} (dummy : nat) (l : mylist A) (default : A) : A -> mylist A :=
  match l with
  | mynil => fun _ => mynil
  | mycons x xs => fun _ => mycons x xs
  end.

Definition test_head_and_tail : nat :=
  let l := mycons 10 (mycons 20 mynil) in
  let f := head_and_tail 0 l 0 in
  let l2 := f 99 in
  length l2.
(** f reconstructs the list [10, 20]. length [10,20] = 2 *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** TEST 3: Closure returned from match that applies a function
    to the tail — forces unique_ptr access and HOF. *)
Fixpoint mymap {A B : Type} (f : A -> B) (l : mylist A) : mylist B :=
  match l with
  | mynil => mynil
  | mycons x xs => mycons (f x) (mymap f xs)
  end.

Definition tail_mapper (dummy : nat) (l : mylist nat) : (nat -> nat) -> mylist nat :=
  match l with
  | mynil => fun _ => mynil
  | mycons x xs => fun f => mycons x (mymap f xs)
  end.

Definition test_tail_mapper : nat :=
  let l := mycons 1 (mycons 2 (mycons 3 mynil)) in
  let f := tail_mapper 0 l in
  let l2 := f (fun n => n * 10) in
  length l2.
(** [1, 20, 30]. length = 3 *)

(** TEST 4: Return a closure that captures BOTH subtrees of a tree.
    Both l and r are unique_ptr fields. *)
Definition both_subtrees (dummy : nat) (t : tree) : bool -> tree :=
  match t with
  | Leaf => fun _ => Leaf
  | Node l v r => fun b => if b then l else r
  end.

Definition test_both_subtrees : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let sel := both_subtrees 0 t in
  tree_sum (sel true) + tree_sum (sel false).
(** sel true = Node Leaf 10 Leaf -> sum = 10
    sel false = Node Leaf 30 Leaf -> sum = 30
    total = 40 *)

(** TEST 5: Chain of closures each pre-computing from the tail. *)
Fixpoint build_chain (l : mylist nat) : mylist (nat -> nat) :=
  match l with
  | mynil => mynil
  | mycons x xs =>
    let rest_len := length xs in
    mycons (fun n => x + rest_len + n) (build_chain xs)
  end.

Fixpoint apply_chain (fns : mylist (nat -> nat)) (x : nat) : nat :=
  match fns with
  | mynil => x
  | mycons f rest => f (apply_chain rest x)
  end.

Definition test_chain : nat :=
  let l := mycons 10 (mycons 20 (mycons 30 mynil)) in
  let fns := build_chain l in
  apply_chain fns 0.
(** build_chain [10,20,30]:
    x=10, rest_len=2: fun n => 12+n
    x=20, rest_len=1: fun n => 21+n
    x=30, rest_len=0: fun n => 30+n
    apply_chain [f1,f2,f3] 0 = f1(f2(f3(0)))
    = f1(f2(30)) = f1(51) = 63 *)

(** TEST 6: Closure captures tail, then tail is used again
    after the closure is created — tests double use. *)
Definition capture_and_reuse (dummy : nat) (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x xs =>
    let f := fun n => length xs + n in
    let tail_len := length xs in
    f x + tail_len
  end.

Definition test_capture_reuse : nat :=
  capture_and_reuse 0 (mycons 5 (mycons 1 (mycons 2 mynil))).
(** xs = [1,2], length = 2. f 5 = 2+5 = 7. tail_len = 2. 7+2 = 9 *)

End MemSafetyProbe6.

Crane Extraction "mem_safety_probe6" MemSafetyProbe6.
