From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe2.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

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

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint mylength {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ rest => 1 + mylength rest
  end.

(** TEST 1: Use value type in both a partial application AND as a constructor arg.
    Tests whether the move analysis correctly handles double-use. *)
Definition dup_tree (t : tree) : tree * nat :=
  (Node t 0 Leaf, sum_values t 0).

Definition test_dup_tree : nat :=
  let t := Node Leaf 42 Leaf in
  let p := dup_tree t in
  sum_values (fst p) 0 + snd p.
(** fst p = Node (Node Leaf 42 Leaf) 0 Leaf, sum_values (fst p) 0 = 42
    snd p = sum_values t 0 = 42. Total = 84 *)

(** TEST 2: CPS-style: pass a continuation that captures value types. *)
Definition with_tree {A : Type} (t : tree) (k : (nat -> nat) -> A) : A :=
  k (sum_values t).

Definition test_cps : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  with_tree t (fun f => f 5 + f 0).
(** f = sum_values t. f 5 = 65, f 0 = 60. Total = 125 *)

(** TEST 3: Compose two closures, each capturing a different tree. *)
Definition compose_adders (t1 t2 : tree) (x : nat) : nat :=
  sum_values t1 (sum_values t2 x).

Definition test_compose : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let f := compose_adders t1 t2 in
  f 5.
(** sum_values t2 5 = 25, sum_values t1 25 = 35. Total = 35 *)

(** TEST 4: Partial application of a wrapper that stores its arg in a constructor. *)
Definition make_node (l : tree) (v : nat) (r : tree) : tree :=
  Node l v r.

Definition test_partial_ctor : nat :=
  let t := Node Leaf 42 Leaf in
  let f := make_node t in
  let t2 := f 99 Leaf in
  sum_values t2 0.
(** t2 = Node (Node Leaf 42 Leaf) 99 Leaf, sum_values t2 0 = 42 *)

(** TEST 5: Closure capturing a closure.
    The inner closure captures a tree, the outer captures the inner closure. *)
Definition double_wrap (t : tree) (x : nat) : nat :=
  let f := sum_values t in
  let g := fun y => f y + y in
  g x.

Definition test_double_wrap : nat :=
  let t := Node Leaf 42 Leaf in
  double_wrap t 10.
(** f 10 = 52, g 10 = 52 + 10 = 62 *)

(** TEST 6: Value type used twice in pair. *)
Definition tree_pair (t : tree) : tree * tree :=
  (t, t).

Definition test_tree_pair : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let p := tree_pair t in
  sum_values (fst p) 0 + sum_values (snd p) 0.
(** Both should be 60. Total = 120 *)

(** TEST 7: Closure escaping through a list, then applied. *)
Fixpoint map_apply (fs : mylist (nat -> nat)) (x : nat) : mylist nat :=
  match fs with
  | mynil => mynil
  | mycons f rest => mycons (f x) (map_apply rest x)
  end.

Fixpoint mysum (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x rest => x + mysum rest
  end.

Definition test_closure_escape_list : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let fs := mycons (sum_values t1) (mycons (sum_values t2) mynil) in
  mysum (map_apply fs 5).
(** (10+5) + (20+5) = 40 *)

(** TEST 8: Match inside let-in where the partial application captures
    a match-bound field AND the match is inside a let continuation.
    Probes interaction between escape analysis and nested match. *)
Definition extract_and_apply (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r =>
    let fl := sum_values l in
    let fr := sum_values r in
    fl v + fr v
  end.

Definition test_extract_apply : nat :=
  extract_and_apply (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).
(** fl = sum_values (Node Leaf 10 Leaf), fr = sum_values (Node Leaf 30 Leaf)
    fl 20 = 10 + 20 = 30, fr 20 = 30 + 20 = 50. Total = 80 *)

(** TEST 9: Option wrapping a closure. *)
Definition opt_adder (t : tree) (b : bool) : option (nat -> nat) :=
  if b then Some (sum_values t) else None.

Definition test_opt_closure : nat :=
  let t := Node Leaf 42 Leaf in
  match opt_adder t true with
  | Some f => f 10
  | None => 0
  end.
(** f = sum_values t, f 10 = 52 *)

(** TEST 10: Two partial applications of the SAME function
    with DIFFERENT captured values. Both must independently own data. *)
Definition test_two_partial : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let f := sum_values t1 in
  let g := sum_values t2 in
  f (g 0).
(** g 0 = 20, f 20 = 30. Total = 30 *)

(** TEST 11: Partial application used in BOTH branches of a match
    (only one branch executes). *)
Definition branch_use (t : tree) (b : bool) : nat :=
  let f := sum_values t in
  if b then f 0 else f 100.

Definition test_branch_true : nat :=
  branch_use (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)) true.
(** f 0 = 60 *)

Definition test_branch_false : nat :=
  branch_use (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)) false.
(** f 100 = 160 *)

(** TEST 12: Value type cloned into pair, then both halves used with closures. *)
Definition clone_and_close (t : tree) : nat :=
  let p := (t, t) in
  let f := sum_values (fst p) in
  let g := sum_values (snd p) in
  f 1 + g 2.
(** With t = Node Leaf 42 Leaf: 43 + 44 = 87 *)

Definition test_clone_close : nat :=
  clone_and_close (Node Leaf 42 Leaf).

(** TEST 13: Fold building tree from closures' results. *)
Fixpoint fold_tree_build (fs : mylist (nat -> nat)) (acc : nat) : tree :=
  match fs with
  | mynil => Leaf
  | mycons f rest => Node (fold_tree_build rest (f acc)) (f acc) Leaf
  end.

Definition test_fold_tree : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let fs := mycons (sum_values t1) (mycons (sum_values t2) mynil) in
  let result := fold_tree_build fs 5 in
  sum_values result 0.
(** f1 5 = 15, f2 15 = 35
    inner: fold_tree_build [f2] 15 = Node Leaf 35 Leaf
    outer: Node (Node Leaf 35 Leaf) 15 Leaf
    sum_values ... 0 = 35 *)

(** TEST 14: Partial application stored in pair alongside tree. *)
Definition pair_closure_tree (t : tree) : (nat -> nat) * tree :=
  (sum_values t, t).

Definition test_pair_closure_tree : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let p := pair_closure_tree t in
  fst p 5 + sum_values (snd p) 0.
(** fst p 5 = 65, sum_values (snd p) 0 = 60. Total = 125 *)

(** TEST 15: Multiple closures applied in sequence, each consuming a tree. *)
Definition apply_chain (t1 t2 t3 : tree) (x : nat) : nat :=
  let f1 := sum_values t1 in
  let f2 := sum_values t2 in
  let f3 := sum_values t3 in
  f3 (f2 (f1 x)).

Definition test_chain : nat :=
  apply_chain (Node Leaf 10 Leaf) (Node Leaf 20 Leaf) (Node Leaf 30 Leaf) 5.
(** f1 5 = 15, f2 15 = 35, f3 35 = 65. Total = 65 *)

(** TEST 16: Closure captured in a match branch that also destructs a tree.
    The closure captures a value-type match-bound field. *)
Definition capture_in_branch (t1 t2 : tree) : nat :=
  match t1 with
  | Leaf => 0
  | Node l v r =>
    let f := sum_values l in
    f v + sum_values r v
  end.

Definition test_capture_branch : nat :=
  capture_in_branch
    (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf))
    Leaf.
(** l = Node Leaf 10 Leaf, v = 20, r = Node Leaf 30 Leaf
    f = sum_values l, f 20 = 30, sum_values r 20 = 50. Total = 80 *)

(** TEST 17: Build a list of closures, reverse it, and apply all.
    Probes whether closures survive list operations. *)
Fixpoint myrev_append {A : Type} (l acc : mylist A) : mylist A :=
  match l with
  | mynil => acc
  | mycons x rest => myrev_append rest (mycons x acc)
  end.

Definition myrev {A : Type} (l : mylist A) : mylist A :=
  myrev_append l mynil.

Fixpoint apply_all (fs : mylist (nat -> nat)) (x : nat) : nat :=
  match fs with
  | mynil => 0
  | mycons f rest => f x + apply_all rest x
  end.

Definition test_rev_closures : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let t3 := Node Leaf 30 Leaf in
  let fs := mycons (sum_values t1) (mycons (sum_values t2)
                    (mycons (sum_values t3) mynil)) in
  let rfs := myrev fs in
  apply_all rfs 5.
(** Reversed order doesn't matter for the sum.
    (30+5) + (20+5) + (10+5) = 75 *)

(** TEST 18: Construct a tree using partial app results, then traverse it. *)
Definition build_from_partial (t : tree) : tree :=
  let v := sum_values t 0 in
  Node (Node Leaf v Leaf) v (Node Leaf v Leaf).

Definition test_build_from_partial : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  let t2 := build_from_partial t in
  sum_values t2 0.
(** v = 60, t2 = Node (Node Leaf 60 Leaf) 60 (Node Leaf 60 Leaf)
    sum_values t2 0 = 60 + 60 + 60 + 0 = 180 *)

End MemSafetyProbe2.

Crane Extraction "mem_safety_probe2" MemSafetyProbe2.
