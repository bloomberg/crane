From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe26.

(** Probe 26: Closures stored in inductives capturing match-bound tree data.

    Attack vector: Force creation of actual closure objects (not inlined)
    by storing them in inductive constructors. The closures capture
    tree children from match bindings, which are structured binding
    references to unique_ptr fields. If Crane fails to create explicit
    value copies, the closures hold dangling references. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** TEST 1: Closure stored in pair, captures tree children from match.
    The closure captures l and r — tree children accessed via unique_ptr.
    The test constructs the pair, then calls the closure after the
    original tree temporary is destroyed. *)
Definition match_to_pair (t : tree) : (nat -> nat) * nat :=
  match t with
  | Leaf => (fun x => x, 0)
  | Node l v r => (fun x => x + tree_sum l + tree_sum r, v)
  end.

Definition test_match_to_pair : nat :=
  let p := match_to_pair (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) in
  fst p 100 + snd p.
(** Expected: (100 + 3 + 11) + 7 = 121 *)

(** TEST 2: Two closures in a pair, each captures a different child.
    Tests that both children are correctly cloned into their
    respective closures. *)
Definition split_closures (t : tree) : (nat -> nat) * (nat -> nat) :=
  match t with
  | Leaf => (fun x => x, fun x => x)
  | Node l v r =>
    (fun x => x + tree_sum l + v,
     fun x => x + v + tree_sum r)
  end.

Definition test_split_closures : nat :=
  let p := split_closures (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) in
  fst p 100 + snd p 200.
(** Expected: (100 + 3 + 7) + (200 + 7 + 11) = 110 + 218 = 328 *)

(** TEST 3: Closure stored in option, captures tree children.
    The option prevents inlining. *)
Definition match_to_option (t : tree) : option (nat -> nat) :=
  match t with
  | Leaf => None
  | Node l v r => Some (fun x => x + tree_sum l + v + tree_sum r)
  end.

Definition test_match_to_option : nat :=
  match match_to_option (Node (Node Leaf 2 Leaf) 5 (Node Leaf 8 Leaf)) with
  | Some f => f 100
  | None => 0
  end.
(** Expected: 100 + 2 + 5 + 8 = 115 *)

(** TEST 4: Recursive function building list of closures.
    Each closure captures tree children from its level. *)
Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint build_tree_closures (t : tree) : mylist (nat -> nat) :=
  match t with
  | Leaf => mynil
  | Node l v r =>
    mycons (fun x => x + tree_sum l + v + tree_sum r)
           (mynil)
  end.

Definition apply_first_closure (l : mylist (nat -> nat)) (x : nat) : nat :=
  match l with
  | mynil => x
  | mycons f _ => f x
  end.

Definition test_build_tree_closures : nat :=
  let closures := build_tree_closures
    (Node (Node Leaf 4 Leaf) 6 (Node Leaf 9 Leaf)) in
  apply_first_closure closures 100.
(** Expected: 100 + 4 + 6 + 9 = 119 *)

(** TEST 5: Closure captures tree child, then child is also used
    elsewhere in the same expression. Tests whether clone is
    independent of the original. *)
Definition closure_and_sum (t : tree) : (nat -> nat) * nat :=
  match t with
  | Leaf => (fun x => x, 0)
  | Node l v r =>
    (fun x => x + tree_sum l, tree_sum l + v + tree_sum r)
  end.

Definition test_closure_and_sum : nat :=
  let p := closure_and_sum (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) in
  fst p 100 + snd p.
(** Expected: (100 + 3) + 21 = 124 *)

(** TEST 6: Closure captures grandchild — two levels of deref.
    ll is accessed via l which is accessed via t. *)
Definition deep_closure_pair (t : tree) : (nat -> nat) * nat :=
  match t with
  | Leaf => (fun x => x, 0)
  | Node l v r =>
    match l with
    | Leaf => (fun x => x + v, 0)
    | Node ll lv lr =>
      (fun x => x + tree_sum ll + lv, v + tree_sum lr)
    end
  end.

Definition test_deep_closure_pair : nat :=
  let p := deep_closure_pair
    (Node (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) 10 Leaf) in
  fst p 100 + snd p.
(** Expected: (100 + 1 + 2) + (10 + 3) = 103 + 13 = 116 *)

(** TEST 7: Closure captures tree child and also uses it immediately
    in an expression — tests clone independence under shared access. *)
Definition shared_child_closure (t : tree) : (nat -> nat) * tree :=
  match t with
  | Leaf => (fun x => x, Leaf)
  | Node l v r => (fun x => x + tree_sum l, l)
  end.

Definition test_shared_child_closure : nat :=
  let p := shared_child_closure (Node (Node Leaf 5 Leaf) 10 Leaf) in
  fst p 100 + tree_sum (snd p).
(** Expected: (100 + 5) + 5 = 110 *)

(** TEST 8: Conditional closure creation — match result determines
    which closure to store. Both branches create closures that
    capture tree data. *)
Definition conditional_closure (t : tree) (n : nat) : (nat -> nat) * nat :=
  match t with
  | Leaf => (fun x => x, 0)
  | Node l v r =>
    if Nat.leb n v
    then (fun x => x + tree_sum l, v)
    else (fun x => x + tree_sum r, v)
  end.

Definition test_conditional_closure : nat :=
  let p1 := conditional_closure
    (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) 5 in
  let p2 := conditional_closure
    (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) 10 in
  fst p1 100 + snd p1 + fst p2 200 + snd p2.
(** p1: n=5 <= v=7, so left: (fun x => x + 3, 7). fst p1 100 = 103, snd p1 = 7
    p2: n=10 > v=7, so right: (fun x => x + 11, 7). fst p2 200 = 211, snd p2 = 7
    Total: 103 + 7 + 211 + 7 = 328 *)

End MemSafetyProbe26.

Crane Extraction "mem_safety_probe26" MemSafetyProbe26.
