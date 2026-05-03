From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe27.

(** Probe 27: Closures capturing whole tree without match.

    Attack vector: Closures stored in data structures that capture
    the whole tree parameter (not through a match). Tests whether
    Crane creates a proper clone when there's no match destructuring
    to trigger the explicit copy mechanism.

    Additional vectors:
    - if/else returning closures (Sif at top level, not Smatch)
    - closures capturing multiple tree parameters
    - closures stored in user-defined inductives *)

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
  | Node l v r => 1 + max (tree_depth l) (tree_depth r)
  end.

(** TEST 1: Pair containing closure that captures whole tree.
    No match on t — just direct capture. Tests whether Crane
    creates a clone of t for the closure. *)
Definition pair_with_fn (t : tree) : (nat -> nat) * nat :=
  (fun x => x + tree_sum t, tree_sum t).

Definition test_pair_with_fn : nat :=
  let p := pair_with_fn (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) in
  fst p 100 + snd p.
(** Expected: (100 + 21) + 21 = 142 *)

(** TEST 2: if/else returning different closures in a pair.
    After IIFE inlining, this becomes a top-level Sif.
    return_captures_by_value may not process inner returns. *)
Definition cond_pair_fn (t : tree) (b : bool) : (nat -> nat) * nat :=
  if b
  then (fun x => x + tree_sum t, 1)
  else (fun x => x + tree_depth t, 2).

Definition test_cond_pair_fn : nat :=
  let p1 := cond_pair_fn (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) true in
  let p2 := cond_pair_fn (Node (Node Leaf 3 Leaf) 7 (Node Leaf 11 Leaf)) false in
  fst p1 100 + snd p1 + fst p2 200 + snd p2.
(** p1: b=true → (fun x => x + 21, 1). fst p1 100 = 121, snd p1 = 1
    p2: b=false → (fun x => x + 2, 2). fst p2 200 = 202, snd p2 = 2
    Total: 121 + 1 + 202 + 2 = 326 *)

(** TEST 3: Closure capturing TWO tree parameters. *)
Definition pair_two_trees (t1 t2 : tree) : (nat -> nat) * nat :=
  (fun x => x + tree_sum t1 + tree_sum t2, tree_sum t1).

Definition test_pair_two_trees : nat :=
  let p := pair_two_trees
    (Node Leaf 5 Leaf)
    (Node Leaf 10 Leaf) in
  fst p 100 + snd p.
(** Expected: (100 + 5 + 10) + 5 = 120 *)

(** TEST 4: Closure stored in option (no match on tree). *)
Definition opt_tree_fn (t : tree) (b : bool) : option (nat -> nat) :=
  if b then Some (fun x => x + tree_sum t) else None.

Definition test_opt_tree_fn : nat :=
  match opt_tree_fn (Node Leaf 15 Leaf) true with
  | Some f => f 100
  | None => 0
  end.
(** Expected: 100 + 15 = 115 *)

(** TEST 5: Nested closures — inner captures tree, outer captures inner.
    Tests that the inner closure correctly clones the tree. *)
Definition nested_closure_pair (t : tree) : (nat -> nat) * nat :=
  let f := fun x => x + tree_sum t in
  (fun x => f (f x), tree_sum t).

Definition test_nested_closure_pair : nat :=
  let p := nested_closure_pair (Node Leaf 5 Leaf) in
  fst p 100 + snd p.
(** Expected: f(f(100)) = f(105) = 110; snd = 5; total = 115 *)

(** TEST 6: Three closures stored in a triple, each using tree differently. *)
Definition triple_fns (t : tree) : (nat -> nat) * (nat -> nat) * nat :=
  (fun x => x + tree_sum t,
   fun x => x + tree_depth t,
   tree_sum t + tree_depth t).

Definition test_triple_fns : nat :=
  let tr := triple_fns (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) in
  fst (fst tr) 100 + snd (fst tr) 200 + snd tr.
(** sum = 6, depth = 2
    Expected: (100 + 6) + (200 + 2) + 8 = 316 *)

(** TEST 7: Closure and tree value stored together in a pair.
    Tests whether the closure's capture and the tree return
    are independent clones. *)
Definition fn_and_tree (t : tree) : (nat -> nat) * tree :=
  (fun x => x + tree_sum t, t).

Definition test_fn_and_tree : nat :=
  let p := fn_and_tree (Node Leaf 7 Leaf) in
  fst p 100 + tree_sum (snd p).
(** Expected: (100 + 7) + 7 = 114 *)

(** TEST 8: Closure captures tree, stored in option inside a pair.
    Multiple levels of wrapping. *)
Definition wrapped_fn (t : tree) (b : bool) : option (nat -> nat) * nat :=
  (if b then Some (fun x => x + tree_sum t) else None,
   tree_sum t).

Definition test_wrapped_fn : nat :=
  let p := wrapped_fn (Node (Node Leaf 2 Leaf) 4 (Node Leaf 6 Leaf)) true in
  match fst p with
  | Some f => f 100 + snd p
  | None => 0
  end.
(** Expected: (100 + 12) + 12 = 124 *)

End MemSafetyProbe27.

Crane Extraction "mem_safety_probe27" MemSafetyProbe27.
