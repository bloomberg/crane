From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe3.

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

(** TEST 1: Local fixpoint capturing a tree value.
    The fixpoint accesses the captured tree on each recursive call. *)
Definition local_fix_capture : nat :=
  let t := Node Leaf 42 Leaf in
  let f := (fix helper (n : nat) : nat :=
    match n with
    | O => sum_values t 0
    | S n' => sum_values t 1 + helper n'
    end) in
  f 3.
(** helper 3 = 43 + helper 2 = 43 + 43 + helper 1 = 43 + 43 + 43 + helper 0
    = 43 + 43 + 43 + 42 = 171 *)

(** TEST 2: Local fixpoint returning a closure that captures
    a match-destructured field from a tree. *)
Definition fix_with_closure : nat :=
  let t := Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf) in
  match t with
  | Leaf => 0
  | Node l v r =>
    let fl := sum_values l in
    let vl := fl v in
    let fr := sum_values r in
    let vr := fr v in
    vl + vr
  end.
(** fl 20 = 10 + 20 = 30, fr 20 = 30 + 20 = 50. Total = 80 *)

(** TEST 3: Partial application result stored in a pair, then both
    elements of the pair are applied. The pair construction must
    properly clone the closures. *)
Definition paired_closures (t1 t2 : tree) : (nat -> nat) * (nat -> nat) :=
  (sum_values t1, sum_values t2).

Definition test_paired_closures : nat :=
  let t1 := Node Leaf 10 Leaf in
  let t2 := Node Leaf 20 Leaf in
  let p := paired_closures t1 t2 in
  fst p 5 + snd p 5.
(** fst p 5 = 15, snd p 5 = 25. Total = 40 *)

(** TEST 4: Tree traversal that builds up a nat accumulator
    using local fixpoint. The tree is captured in the fixpoint scope. *)
Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

Definition test_tree_sum : nat :=
  tree_sum (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).
(** 10 + 20 + 30 = 60 *)

(** TEST 5: Mutual use: tree used BOTH as partial application arg
    AND as match scrutinee in the SAME scope. *)
Definition mutual_use (t : tree) : nat :=
  let f := sum_values t in
  let r := match t with
    | Leaf => 0
    | Node _ v _ => v
    end in
  f r.
(** f = sum_values (Node (Node Leaf 10 Leaf) 20 (...))
    r = 20. f 20 = 10+30+20+20 = 80 *)

Definition test_mutual_use : nat :=
  mutual_use (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf)).

(** TEST 6: Nested pair: pair of pairs of closures. *)
Definition nested_pair (t : tree) : ((nat -> nat) * (nat -> nat)) * nat :=
  ((sum_values t, fun x => x), sum_values t 0).

Definition test_nested_pair : nat :=
  let t := Node Leaf 42 Leaf in
  let p := nested_pair t in
  fst (fst p) 10 + snd (fst p) 10 + snd p.
(** fst (fst p) 10 = 52, snd (fst p) 10 = 10, snd p = 42. Total = 104 *)

(** TEST 7: Map a tree, producing a new tree. Then sum the new tree.
    The mapped function captures a tree value. *)
Fixpoint map_tree (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (map_tree f l) (f v) (map_tree f r)
  end.

Definition test_map_with_captured : nat :=
  let t := Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf) in
  let t2 := Node Leaf 100 Leaf in
  let mapped := map_tree (fun v => v + sum_values t2 0) t in
  tree_sum mapped.
(** sum_values t2 0 = 100. map adds 100 to each node value.
    mapped = Node (Node Leaf 105 Leaf) 110 (Node Leaf 115 Leaf)
    tree_sum mapped = 105 + 110 + 115 = 330 *)

(** TEST 8: Three closures, each capturing different tree,
    applied in a specific order with results feeding forward. *)
Definition chain_three (t1 t2 t3 : tree) : nat :=
  let f1 := sum_values t1 in
  let f2 := sum_values t2 in
  let f3 := sum_values t3 in
  f3 (f2 (f1 0)).

Definition test_chain_three : nat :=
  chain_three (Node Leaf 10 Leaf) (Node Leaf 20 Leaf) (Node Leaf 30 Leaf).
(** f1 0 = 10, f2 10 = 30, f3 30 = 60. Total = 60 *)

(** TEST 9: Closure stored in option alongside tree data in pair. *)
Definition opt_pair (t : tree) (b : bool) : option (nat -> nat) * tree :=
  (if b then Some (sum_values t) else None, t).

Definition test_opt_pair : nat :=
  let t := Node Leaf 42 Leaf in
  let p := opt_pair t true in
  match fst p with
  | Some f => f 10 + sum_values (snd p) 0
  | None => 0
  end.
(** f 10 = 52, sum_values (snd p) 0 = 42. Total = 94 *)

(** TEST 10: Large tree with deep recursion — stresses the
    loopified tree traversal and clone mechanisms. *)
Fixpoint build_deep (n : nat) : tree :=
  match n with
  | O => Leaf
  | S n' => Node (build_deep n') n Leaf
  end.

Definition test_deep_tree : nat :=
  let t := build_deep 100 in
  tree_sum t.
(** Sum of 1 + 2 + ... + 100 = 5050 *)

(** TEST 11: Fixpoint that takes a function argument and uses it
    alongside captured tree data. *)
Fixpoint apply_n_times (f : nat -> nat) (n : nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => f (apply_n_times f n' x)
  end.

Definition test_apply_n : nat :=
  let t := Node Leaf 10 Leaf in
  apply_n_times (sum_values t) 5 0.
(** f = sum_values t = fun x => 10 + x
    f(f(f(f(f(0))))) = f(f(f(f(10)))) = f(f(f(20))) = f(f(30)) = f(40) = 50 *)

(** TEST 12: Closure that partially applies a fixpoint.
    The fixpoint itself takes a function argument. *)
Definition test_partial_fix : nat :=
  let t := Node Leaf 5 Leaf in
  let f := apply_n_times (sum_values t) 3 in
  f 0 + f 10.
(** f 0 = apply_n_times (sum_values t) 3 0 = f(f(f(0))) = 5+5+5 = 15
    f 10 = apply_n_times (sum_values t) 3 10 = 5+5+5+10 = 25. Total = 40 *)

End MemSafetyProbe3.

Crane Extraction "mem_safety_probe3" MemSafetyProbe3.
