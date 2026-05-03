From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe29.

(** Probe 29: Exotic inductive types and clone/destructor correctness.

    Attack vectors:
    - Value types nested inside other value types (inner tree as field of outer tree)
    - Multiple constructors with varying numbers of recursive fields
    - Mixed recursive and non-recursive fields
    - Dup pattern (using a value twice → exercises copy constructor)
    - Rebuild pattern (transforming tree in-place → exercises move/copy interaction) *)

(** An inner tree type — value type with recursive children. *)
Inductive inner : Type :=
| ILeaf : inner
| INode : inner -> nat -> inner -> inner.

Fixpoint inner_sum (t : inner) : nat :=
  match t with
  | ILeaf => 0
  | INode l v r => inner_sum l + v + inner_sum r
  end.

(** An outer tree type with an inner tree as a non-recursive field. *)
Inductive outer : Type :=
| OLeaf : outer
| ONode : outer -> inner -> outer -> outer.

Fixpoint outer_sum (t : outer) : nat :=
  match t with
  | OLeaf => 0
  | ONode l i r => outer_sum l + inner_sum i + outer_sum r
  end.

(** An expression type with varying constructor arities. *)
Inductive expr : Type :=
| Lit : nat -> expr
| Neg : expr -> expr
| Add : expr -> expr -> expr
| Mul : expr -> expr -> expr.

Fixpoint eval_expr (e : expr) : nat :=
  match e with
  | Lit n => n
  | Neg a => eval_expr a
  | Add a b => eval_expr a + eval_expr b
  | Mul a b => eval_expr a * eval_expr b
  end.

(** A three-child tree. *)
Inductive tree3 : Type :=
| T3Leaf : tree3
| T3Node : tree3 -> tree3 -> tree3 -> nat -> tree3.

Fixpoint tree3_sum (t : tree3) : nat :=
  match t with
  | T3Leaf => 0
  | T3Node a b c v => tree3_sum a + tree3_sum b + tree3_sum c + v
  end.

(** TEST 1: Build and sum an outer tree with inner tree values.
    Tests nested value-type clone/destructor interaction. *)
Definition test_outer_basic : nat :=
  let o := ONode
    (ONode OLeaf (INode ILeaf 10 ILeaf) OLeaf)
    (INode (INode ILeaf 1 ILeaf) 2 (INode ILeaf 3 ILeaf))
    (ONode OLeaf (INode ILeaf 20 ILeaf) OLeaf) in
  outer_sum o.
(** Expected: 0 + 10 + 0 + (1+2+3) + 0 + 20 + 0 = 36 *)

(** TEST 2: Dup pattern — use inner tree twice in outer construction. *)
Definition dup_inner (i : inner) : outer :=
  ONode (ONode OLeaf i OLeaf) i (ONode OLeaf i OLeaf).

Definition test_dup_inner : nat :=
  let i := INode (INode ILeaf 5 ILeaf) 10 (INode ILeaf 15 ILeaf) in
  outer_sum (dup_inner i).
(** i_sum = 5 + 10 + 15 = 30
    outer_sum = 0 + 30 + 0 + 30 + 0 + 30 + 0 = 90 *)

(** TEST 3: Transform outer tree — rebuild with modified inner values. *)
Fixpoint double_inner (i : inner) : inner :=
  match i with
  | ILeaf => ILeaf
  | INode l v r => INode (double_inner l) (v * 2) (double_inner r)
  end.

Fixpoint transform_outer (t : outer) : outer :=
  match t with
  | OLeaf => OLeaf
  | ONode l i r => ONode (transform_outer l) (double_inner i) (transform_outer r)
  end.

Definition test_transform : nat :=
  let o := ONode
    OLeaf
    (INode ILeaf 5 ILeaf)
    (ONode OLeaf (INode ILeaf 10 ILeaf) OLeaf) in
  outer_sum (transform_outer o).
(** After transform: inner values doubled.
    = 0 + 10 + (0 + 20 + 0) = 30 *)

(** TEST 4: Build and evaluate a complex expression tree. *)
Definition test_expr : nat :=
  let e := Add
    (Mul (Add (Lit 2) (Lit 3)) (Lit 4))
    (Neg (Add (Lit 10) (Lit 5))) in
  eval_expr e.
(** (2+3)*4 + (-(10+5)) = 20 + ... neg is tricky in nat.
    Actually, Neg with nat just returns the value (no negation).
    eval_expr (Neg a) = eval_expr a
    So: eval_expr (Add (Mul (Add (Lit 2) (Lit 3)) (Lit 4)) (Neg (Add (Lit 10) (Lit 5))))
    = eval_expr (Mul (Add (Lit 2) (Lit 3)) (Lit 4)) + eval_expr (Neg (Add (Lit 10) (Lit 5)))
    = (2+3)*4 + (10+5) = 20 + 15 = 35 *)

(** TEST 5: Deep 3-child tree to stress clone/destructor. *)
Fixpoint build_tree3 (n : nat) : tree3 :=
  match n with
  | O => T3Leaf
  | S n' => T3Node (build_tree3 n') (build_tree3 n') (build_tree3 n') n
  end.

Definition test_tree3 : nat :=
  tree3_sum (build_tree3 4).

(** TEST 6: Dup outer tree — use outer value twice. *)
Definition dup_outer (t : outer) : outer * outer := (t, t).

Definition test_dup_outer : nat :=
  let o := ONode OLeaf (INode ILeaf 42 ILeaf) OLeaf in
  let p := dup_outer o in
  outer_sum (fst p) + outer_sum (snd p).
(** 42 + 42 = 84 *)

(** TEST 7: Map over expr tree — rebuild with transformed values. *)
Fixpoint double_expr (e : expr) : expr :=
  match e with
  | Lit n => Lit (n * 2)
  | Neg a => Neg (double_expr a)
  | Add a b => Add (double_expr a) (double_expr b)
  | Mul a b => Mul (double_expr a) (double_expr b)
  end.

Definition test_double_expr : nat :=
  eval_expr (double_expr (Add (Lit 5) (Mul (Lit 3) (Lit 7)))).
(** double_expr: Lit values doubled → Add (Lit 10) (Mul (Lit 6) (Lit 14))
    eval: 10 + 6*14 = 10 + 84 = 94 *)

(** TEST 8: Mixed operations — build outer from expr eval results,
    then transform. Cross-type interaction. *)
Fixpoint expr_to_inner (e : expr) : inner :=
  match e with
  | Lit n => INode ILeaf n ILeaf
  | Neg a => expr_to_inner a
  | Add a b => INode (expr_to_inner a) 0 (expr_to_inner b)
  | Mul a b => INode (expr_to_inner a) 1 (expr_to_inner b)
  end.

Definition test_cross_type : nat :=
  let e := Add (Lit 5) (Mul (Lit 3) (Lit 7)) in
  let i := expr_to_inner e in
  let o := ONode OLeaf i OLeaf in
  outer_sum o + inner_sum i.
(** expr_to_inner (Add (Lit 5) (Mul (Lit 3) (Lit 7)))
    = INode (INode ILeaf 5 ILeaf) 0 (INode (INode ILeaf 3 ILeaf) 1 (INode ILeaf 7 ILeaf))
    inner_sum = 5 + 0 + 3 + 1 + 7 = 16
    outer_sum = 0 + 16 + 0 = 16
    Total = 16 + 16 = 32 *)

End MemSafetyProbe29.

Crane Extraction "mem_safety_probe29" MemSafetyProbe29.
