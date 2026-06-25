From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module AccumClosureEscape.

(** This test explores closure escape through ACCUMULATOR patterns,
    which are different from the direct-return-in-constructor pattern
    tested by the other wip tests.

    Key difference: closures are built up in an accumulator during
    recursion. Each recursive step adds a new closure to a list.
    The closures capture pattern variables from the current match
    scope, which may be references into shared_ptr nodes. *)

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A}.

(** A simple tree for supplying values. *)
Inductive tree : Type :=
| TLeaf : tree
| TNode : tree -> nat -> tree -> tree.

Fixpoint mylist_append {A : Type} (l1 l2 : mylist A) : mylist A :=
  match l1 with
  | mynil => l2
  | mycons h t => mycons h (mylist_append t l2)
  end.

Fixpoint tree_to_list (t : tree) : mylist nat :=
  match t with
  | TLeaf => mynil
  | TNode l v r =>
    mycons v (mylist_append (tree_to_list l) (tree_to_list r))
  end.

(** Fold-left that builds a closure from each element.

    SIMPLE LAMBDA VERSION: Each closure [fun x => h + x] captures
    [h] from the pattern match. These are simple lambdas, so they
    should capture by [=]. *)
Fixpoint build_adders (l : mylist nat) (acc : mylist (nat -> nat))
  : mylist (nat -> nat) :=
  match l with
  | mynil => acc
  | mycons h t => build_adders t (mycons (fun x => h + x) acc)
  end.

(** Apply first closure from the list. *)
Definition apply_first (fns : mylist (nat -> nat)) (x : nat) : nat :=
  match fns with
  | mynil => 0
  | mycons f _ => f x
  end.

(** Apply all closures and sum. *)
Fixpoint apply_all_sum (fns : mylist (nat -> nat)) (x : nat) : nat :=
  match fns with
  | mynil => 0
  | mycons f rest => f x + apply_all_sum rest x
  end.

(** test1: build_adders [10, 20, 30] [] = [30+_, 20+_, 10+_] (reversed)
    apply_first result 5 = 30 + 5 = 35 *)
Definition test1 : nat :=
  let fns := build_adders (mycons 10 (mycons 20 (mycons 30 mynil))) mynil in
  apply_first fns 5.

(** test2: apply all closures: (30+5) + (20+5) + (10+5) = 35+25+15 = 75 *)
Definition test2 : nat :=
  let fns := build_adders (mycons 10 (mycons 20 (mycons 30 mynil))) mynil in
  apply_all_sum fns 5.

(** COMPOSE CLOSURES: Each step builds a composed function.
    This creates closures that capture OTHER closures. *)
Fixpoint compose_from_list (l : mylist nat) (acc : nat -> nat) : nat -> nat :=
  match l with
  | mynil => acc
  | mycons h t => compose_from_list t (fun x => acc (h + x))
  end.

(** test3: compose_from_list [10, 20, 30] id
    = fun x => id (10 + (20 + (30 + x)))
    = fun x => 60 + x
    test3 = 60 + 7 = 67 *)
Definition test3 : nat :=
  compose_from_list (mycons 10 (mycons 20 (mycons 30 mynil))) (fun x => x) 7.

(** Build closures from TREE traversal: tree nodes become closures.
    Each closure captures pattern variables from tree match. *)
Fixpoint tree_to_adders (t : tree) : mylist (nat -> nat) :=
  match t with
  | TLeaf => mynil
  | TNode l v r =>
    mycons (fun x => v + x)
      (mylist_append
        (tree_to_adders l)
        (tree_to_adders r))
  end.

(** test4: Tree (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf))
    Closures: [20+_, 10+_, 30+_]
    apply_all_sum with 5: (20+5) + (10+5) + (30+5) = 25+15+35 = 75 *)
Definition test4 : nat :=
  let t := TNode (TNode TLeaf 10 TLeaf) 20 (TNode TLeaf 30 TLeaf) in
  apply_all_sum (tree_to_adders t) 5.

(** Store a closure and then clobber the stack before using it. *)
Definition test5 : nat :=
  let t := TNode (TNode TLeaf 42 TLeaf) 100 TLeaf in
  let fns := tree_to_adders t in
  let noise := TNode TLeaf 999 TLeaf in
  let _ := tree_to_adders noise in
  apply_first fns 0.

End AccumClosureEscape.

Crane Extraction "accum_closure_escape" AccumClosureEscape.
