From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe25.

(** Probe 25: Closure capture of match-bound value-type variables.

    Attack vector: When a function matches on a value type and returns
    a closure from inside the match branch, the closure captures
    structured-binding references (d_a0, d_a1, d_a2). After IIFE
    inlining, return_captures_by_value may miss the lambda inside
    the Smatch branches, leaving [&] capture. The closure then holds
    dangling references to the function's local structured bindings. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** TEST 1: Return closure that captures the whole tree parameter.
    The closure body calls tree_sum on t. If t is passed by const ref
    and the closure uses [&], t's binding dangles when function returns.
    The test calls the closure AFTER the tree temporary is destroyed. *)
Definition make_sum_fn (t : tree) : nat -> nat :=
  fun x => x + tree_sum t.

Definition test_make_sum_fn : nat :=
  let f := make_sum_fn (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) in
  f 100.
(** Expected: 100 + 21 = 121 *)

(** TEST 2: Return closure from match branch — captures children.
    After IIFE inlining, the Smatch is at the top level, and
    return_captures_by_value may not traverse into it. *)
Definition match_closure (t : tree) : nat -> nat :=
  match t with
  | Leaf => fun x => x
  | Node l v r => fun x => x + tree_sum l + v + tree_sum r
  end.

Definition test_match_closure : nat :=
  let f := match_closure (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) in
  f 100.
(** Expected: 100 + 3 + 7 + 11 = 121 *)

(** TEST 3: Return PAIR of closures from match.
    Each closure captures different match-bound children. *)
Definition pair_closures (t : tree) : (nat -> nat) * (nat -> nat) :=
  match t with
  | Leaf => (fun x => x, fun x => x)
  | Node l v r => (fun x => x + tree_sum l, fun x => x + tree_sum r)
  end.

Definition test_pair_closures : nat :=
  let p := pair_closures (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) in
  fst p 100 + snd p 200.
(** Expected: (100 + 3) + (200 + 11) = 314 *)

(** TEST 4: Nested match returning closure. Both match levels
    contribute captured variables to the closure. *)
Definition nested_match_closure (t1 t2 : tree) : nat -> nat :=
  match t1 with
  | Leaf => fun x => x
  | Node l1 v1 r1 =>
    match t2 with
    | Leaf => fun x => x + v1
    | Node l2 v2 r2 => fun x => x + tree_sum l1 + v2 + tree_sum r2
    end
  end.

Definition test_nested_match_closure : nat :=
  let f := nested_match_closure
    (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf))
    (Node (Node Leaf 2 Leaf) 5 (Node Leaf 8 Leaf)) in
  f 100.
(** Expected: 100 + 3 + 5 + 8 = 116 *)

(** TEST 5: Deep match — closure captures grandchild of tree.
    ll is child-of-child, accessed via two levels of unique_ptr deref. *)
Definition deep_match_closure (t : tree) : nat -> nat :=
  match t with
  | Leaf => fun x => x
  | Node l v r =>
    match l with
    | Leaf => fun x => x + v
    | Node ll lv lr => fun x => x + tree_sum ll + lv + v
    end
  end.

Definition test_deep_match_closure : nat :=
  let f := deep_match_closure
    (Node (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) 10 Leaf) in
  f 100.
(** inner match: l = Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)
    ll = Node Leaf 1 Leaf, lv = 2, v = 10
    Expected: 100 + tree_sum(Node Leaf 1 Leaf) + 2 + 10 = 100 + 1 + 2 + 10 = 113 *)

(** TEST 6: Build a list of closures from recursive tree traversal.
    Each closure captures v from the current node.
    Tests whether closures stored in constructor fields are safe. *)
Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint build_adders (t : tree) : mylist (nat -> nat) :=
  match t with
  | Leaf => mynil
  | Node l v r =>
    mycons (fun x => x + v) (mynil)
  end.

Definition apply_first (l : mylist (nat -> nat)) (x : nat) : nat :=
  match l with
  | mynil => x
  | mycons f _ => f x
  end.

Definition test_build_adders : nat :=
  let adders := build_adders (Node Leaf 42 Leaf) in
  apply_first adders 100.
(** Expected: 100 + 42 = 142 *)

(** TEST 7: Return closure from match that captures a tree child,
    then store it in a pair. Double-wrapping test. *)
Definition match_then_pair (t : tree) : (nat -> nat) * nat :=
  let f := match t with
           | Leaf => fun x => x
           | Node l v r => fun x => x + tree_sum l + v
           end in
  (f, tree_sum t).

Definition test_match_then_pair : nat :=
  let p := match_then_pair (Node (Node Leaf 4 Leaf) 6 (Node Leaf 9 Leaf)) in
  fst p 100 + snd p.
(** Expected: (100 + 4 + 6) + 19 = 129 *)

(** TEST 8: Option wrapping a closure from match.
    Exercises different code path for returning closures
    through an inductive constructor. *)
Definition match_closure_opt (t : tree) (b : bool) : option (nat -> nat) :=
  if b then
    Some (match t with
          | Leaf => fun x => x
          | Node l v r => fun x => x + tree_sum l + v + tree_sum r
          end)
  else
    None.

Definition test_match_closure_opt : nat :=
  match match_closure_opt (Node (Node Leaf 2 Leaf) 5 (Node Leaf 8 Leaf)) true with
  | Some f => f 100
  | None => 0
  end.
(** Expected: 100 + 2 + 5 + 8 = 115 *)

End MemSafetyProbe25.

Crane Extraction "mem_safety_probe25" MemSafetyProbe25.
