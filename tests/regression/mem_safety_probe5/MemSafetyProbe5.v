From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe5.

(** These tests probe interactions between:
    - Closures that access nested fields of value types
    - Loopification storing closures in frames
    - The body_derefs_var override in cpp_print.ml *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

(** A function that accesses a NESTED field — forces a
    dereference of a unique_ptr inside the lambda body. *)
Definition get_left_val (t : tree) (default : nat) : nat :=
  match t with
  | Leaf => default
  | Node l _ _ =>
    match l with
    | Leaf => default
    | Node _ v _ => v
    end
  end.

(** TEST 1: Partial app of get_left_val, applied to recursive result.
    The closure body accesses nested tree structure. *)
Fixpoint sum_left_vals (l : mylist tree) : nat :=
  match l with
  | mynil => 0
  | mycons t xs =>
    let f := get_left_val t in
    f (sum_left_vals xs)
  end.

Definition test_sum_left : nat :=
  sum_left_vals (mycons (Node (Node Leaf 10 Leaf) 20 Leaf)
                (mycons (Node (Node Leaf 30 Leaf) 40 Leaf)
                (mycons (Node Leaf 50 Leaf) mynil))).
(** f1 captures Node (Node Leaf 10 Leaf) 20 Leaf.
    get_left_val returns 10 when default >= 10? No.
    get_left_val (Node (Node Leaf 10 Leaf) 20 Leaf) default:
      l = Node Leaf 10 Leaf -> match l: Node _ v _ -> v = 10. So f1 _ = 10.
    get_left_val (Node (Node Leaf 30 Leaf) 40 Leaf) default:
      l = Node Leaf 30 Leaf -> v = 30. So f2 _ = 30.
    get_left_val (Node Leaf 50 Leaf) default:
      l = Leaf -> default. So f3 x = x.
    sum_left_vals = f1(f2(f3(0))) = f1(f2(0)) = f1(30) = 10. *)

(** TEST 2: Build a list of partial apps from trees, then apply all.
    Each partial app captures a tree with nested structure. *)
Fixpoint build_getters (l : mylist tree) : mylist (nat -> nat) :=
  match l with
  | mynil => mynil
  | mycons t xs => mycons (get_left_val t) (build_getters xs)
  end.

Fixpoint apply_all (l : mylist (nat -> nat)) (x : nat) : nat :=
  match l with
  | mynil => x
  | mycons f xs => f (apply_all xs x)
  end.

Definition test_build_apply : nat :=
  let trees := mycons (Node (Node Leaf 10 Leaf) 20 Leaf)
               (mycons (Node (Node Leaf 30 Leaf) 40 Leaf)
               (mycons (Node Leaf 50 Leaf) mynil)) in
  let getters := build_getters trees in
  apply_all getters 0.
(** Same computation as test1: 10 *)

(** TEST 3: Pair a partial app with its tree, use both after
    the tree might have been moved. *)
Definition pair_and_apply (t : tree) : nat :=
  let f := get_left_val t in
  let v := match t with
    | Leaf => 0
    | Node _ v _ => v
    end in
  f v.

Definition test_pair_apply : nat :=
  pair_and_apply (Node (Node Leaf 10 Leaf) 20 Leaf).
(** f = get_left_val t = returns 10 always.
    v = 20. f 20 = 10. *)

(** TEST 4: Deep tree with closures at each level. *)
Fixpoint tree_size (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l _ r => 1 + tree_size l + tree_size r
  end.

Fixpoint collect_left_vals (t : tree) (acc : mylist (nat -> nat))
  : mylist (nat -> nat) :=
  match t with
  | Leaf => acc
  | Node l v r =>
    collect_left_vals l
      (collect_left_vals r (mycons (get_left_val t) acc))
  end.

Definition test_collect : nat :=
  let t := Node (Node (Node Leaf 5 Leaf) 10 Leaf)
               15
               (Node Leaf 20 (Node Leaf 25 Leaf)) in
  let fns := collect_left_vals t mynil in
  apply_all fns 0.
(** Tree structure:
         15
        /  \
       10   20
      /      \
     5        25

    Traversal order (collect_left_vals):
    At root (15): get_left_val (Node (Node ..5..) 15 (Node ..20..))
      -> left = Node ..5.., v=5. Returns 5.
    At left child (10): get_left_val (Node (Node Leaf 5 Leaf) 10 Leaf)
      -> left = Node Leaf 5 Leaf, v=5. Returns 5.
    At left-left (5): get_left_val (Node Leaf 5 Leaf)
      -> left = Leaf. Returns default.
    At right child (20): get_left_val (Node Leaf 20 (Node Leaf 25 Leaf))
      -> left = Leaf. Returns default.
    At right-right (25): get_left_val (Node Leaf 25 Leaf)
      -> left = Leaf. Returns default.

    fns = [getter_leftleft, getter_left, getter_rightright, getter_right, getter_root]
    = [id, (const 5), id, id, (const 5)]
    apply_all [id, (const 5), id, id, (const 5)] 0
    = id(const5(id(id(const5(0))))) = id(const5(id(id(5)))) = id(const5(id(5)))
    = id(const5(5)) = id(5) = 5 *)

(** TEST 6: Stress test with very large list of trees. *)
Fixpoint make_tree_list (n : nat) : mylist tree :=
  match n with
  | O => mynil
  | S n' => mycons (Node (Node Leaf n Leaf) (n * 2) Leaf) (make_tree_list n')
  end.

Fixpoint sum_getters (l : mylist (nat -> nat)) (x : nat) : nat :=
  match l with
  | mynil => 0
  | mycons f xs => f x + sum_getters xs x
  end.

Definition test_stress : nat :=
  let trees := make_tree_list 50 in
  let getters := build_getters trees in
  sum_getters getters 0.
(** Each tree Node (Node Leaf n Leaf) (n*2) Leaf: get_left_val returns n.
    Sum of 1 + 2 + ... + 50 = 1275 *)

End MemSafetyProbe5.

Crane Extraction "mem_safety_probe5" MemSafetyProbe5.
