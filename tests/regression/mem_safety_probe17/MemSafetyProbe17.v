From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe17.

(** Probe 17: Wide tree (4-ary) and complex ownership patterns.

    Attack vectors:
    1. 4-ary tree with 4 unique_ptr children -- more complex frame structs
    2. Functions that use ALL children in computations AND recursive calls
    3. Owned match where one child is used in a closure AND others
       in recursive calls (testing pre-extraction with many children)
    4. Mutual-like patterns where different functions process the
       same tree differently *)

Inductive qtree : Type :=
| QLeaf : qtree
| QNode : qtree -> qtree -> nat -> qtree -> qtree -> qtree.

Fixpoint qtree_sum (t : qtree) : nat :=
  match t with
  | QLeaf => 0
  | QNode a b v c d => qtree_sum a + qtree_sum b + v + qtree_sum c + qtree_sum d
  end.

Fixpoint qtree_depth (t : qtree) : nat :=
  match t with
  | QLeaf => 0
  | QNode a b _ c d =>
    let da := qtree_depth a in
    let db := qtree_depth b in
    let dc := qtree_depth c in
    let dd := qtree_depth d in
    let m1 := if Nat.leb da db then db else da in
    let m2 := if Nat.leb dc dd then dd else dc in
    1 + (if Nat.leb m1 m2 then m2 else m1)
  end.

Fixpoint qtree_size (t : qtree) : nat :=
  match t with
  | QLeaf => 0
  | QNode a b _ c d => 1 + qtree_size a + qtree_size b + qtree_size c + qtree_size d
  end.

(** TEST 1: Sum of a 4-ary tree. Basic correctness. *)
Definition test_qtree_sum : nat :=
  let t := QNode
    (QNode QLeaf QLeaf 1 QLeaf QLeaf)
    (QNode QLeaf QLeaf 2 QLeaf QLeaf)
    10
    (QNode QLeaf QLeaf 3 QLeaf QLeaf)
    (QNode QLeaf QLeaf 4 QLeaf QLeaf) in
  qtree_sum t.
(** 1 + 2 + 10 + 3 + 4 = 20 *)

(** TEST 2: Depth of a deep 4-ary tree. *)
Definition test_qtree_depth : nat :=
  let inner := QNode QLeaf QLeaf 1 QLeaf QLeaf in
  let t := QNode inner (QNode inner QLeaf 2 QLeaf QLeaf) 3 QLeaf QLeaf in
  qtree_depth t.
(** inner depth = 1.
    QNode(inner, QNode(inner,...), 3, Leaf, Leaf)
    depths: da=1, db=2, dc=0, dd=0.
    m1=max(1,2)=2, m2=max(0,0)=0.
    depth = 1 + max(2,0) = 3 *)

(** TEST 3: Mirror a 4-ary tree (reverse children order). *)
Fixpoint qtree_mirror (t : qtree) : qtree :=
  match t with
  | QLeaf => QLeaf
  | QNode a b v c d =>
    QNode (qtree_mirror d) (qtree_mirror c) v (qtree_mirror b) (qtree_mirror a)
  end.

Definition test_qtree_mirror : nat :=
  let t := QNode
    (QNode QLeaf QLeaf 1 QLeaf QLeaf)
    QLeaf 10
    (QNode QLeaf QLeaf 3 QLeaf QLeaf)
    QLeaf in
  qtree_sum (qtree_mirror t).
(** mirror preserves sum. Sum = 1 + 10 + 3 = 14 *)

(** TEST 4: Flatten a 4-ary tree to a list (inorder traversal).
    Uses all 4 children in recursive calls + value in list construction. *)
Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint myapp {A : Type} (l1 l2 : mylist A) : mylist A :=
  match l1 with
  | mynil => l2
  | mycons x xs => mycons x (myapp xs l2)
  end.

Fixpoint sum_list (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x xs => x + sum_list xs
  end.

Fixpoint qtree_flatten (t : qtree) : mylist nat :=
  match t with
  | QLeaf => mynil
  | QNode a b v c d =>
    myapp (qtree_flatten a)
      (myapp (qtree_flatten b)
        (mycons v
          (myapp (qtree_flatten c) (qtree_flatten d))))
  end.

Definition test_qtree_flatten : nat :=
  let t := QNode
    (QNode QLeaf QLeaf 1 QLeaf QLeaf)
    (QNode QLeaf QLeaf 2 QLeaf QLeaf)
    5
    (QNode QLeaf QLeaf 3 QLeaf QLeaf)
    (QNode QLeaf QLeaf 4 QLeaf QLeaf) in
  sum_list (qtree_flatten t).
(** All values present: 1+2+5+3+4 = 15 *)

(** TEST 5: Zip two 4-ary trees. *)
Fixpoint qtree_zip (t1 t2 : qtree) : qtree :=
  match t1 with
  | QLeaf => t2
  | QNode a1 b1 v1 c1 d1 =>
    match t2 with
    | QLeaf => t1
    | QNode a2 b2 v2 c2 d2 =>
      QNode (qtree_zip a1 a2) (qtree_zip b1 b2) (v1 + v2)
            (qtree_zip c1 c2) (qtree_zip d1 d2)
    end
  end.

Definition test_qtree_zip : nat :=
  let t1 := QNode QLeaf QLeaf 10 QLeaf QLeaf in
  let t2 := QNode QLeaf QLeaf 20 QLeaf QLeaf in
  qtree_sum (qtree_zip t1 t2).
(** 10 + 20 = 30 *)

(** TEST 6: Compute a value using ALL children non-recursively,
    THEN use all children recursively. Tests frame saving with
    many unique_ptr fields. *)
Fixpoint weighted_sum (t : qtree) : nat :=
  match t with
  | QLeaf => 0
  | QNode a b v c d =>
    let local_weight := qtree_sum a + 2 * qtree_sum b + 3 * v + 4 * qtree_sum c + 5 * qtree_sum d in
    local_weight + weighted_sum a + weighted_sum b + weighted_sum c + weighted_sum d
  end.

Definition test_weighted : nat :=
  let t := QNode
    (QNode QLeaf QLeaf 1 QLeaf QLeaf)
    (QNode QLeaf QLeaf 2 QLeaf QLeaf)
    3
    (QNode QLeaf QLeaf 4 QLeaf QLeaf)
    (QNode QLeaf QLeaf 5 QLeaf QLeaf) in
  weighted_sum t.
(** Root: local_weight = 1 + 2*2 + 3*3 + 4*4 + 5*5 = 1+4+9+16+25 = 55
    weighted a = 3*1 = 3
    weighted b = 3*2 = 6
    weighted c = 3*4 = 12
    weighted d = 3*5 = 15
    Total = 55 + 3 + 6 + 12 + 15 = 91 *)

(** TEST 7: Build a 4-ary tree programmatically and check. *)
Fixpoint make_qtree (n : nat) : qtree :=
  match n with
  | O => QLeaf
  | S n' => QNode (make_qtree n') QLeaf n (make_qtree n') QLeaf
  end.

Definition test_make_qtree : nat :=
  qtree_sum (make_qtree 4).
(** make_qtree 0 = QLeaf (sum=0)
    make_qtree 1 = QNode QLeaf QLeaf 1 QLeaf QLeaf (sum=1)
    Wait: make_qtree 1 = QNode (make_qtree 0) QLeaf 1 (make_qtree 0) QLeaf
        = QNode QLeaf QLeaf 1 QLeaf QLeaf (sum=1)
    make_qtree 2 = QNode (make_qtree 1) QLeaf 2 (make_qtree 1) QLeaf
        = QNode (sum1) QLeaf 2 (sum1) QLeaf
        sum = 1 + 2 + 1 = 4
    make_qtree 3 = sum = 4 + 3 + 4 = 11
    make_qtree 4 = sum = 11 + 4 + 11 = 26 *)

(** TEST 8: Two-pass on a 4-ary tree: flatten then sum vs direct sum. *)
Definition test_two_pass_qtree : nat :=
  let t := QNode
    (QNode QLeaf QLeaf 1 QLeaf QLeaf)
    (QNode QLeaf QLeaf 2 QLeaf QLeaf)
    5
    (QNode QLeaf QLeaf 3 QLeaf QLeaf)
    (QNode QLeaf QLeaf 4 QLeaf QLeaf) in
  sum_list (qtree_flatten t) + qtree_sum t.
(** Both should be 15. Total = 30 *)

End MemSafetyProbe17.

Crane Extraction "mem_safety_probe17" MemSafetyProbe17.
