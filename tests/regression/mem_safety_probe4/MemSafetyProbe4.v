From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe4.

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

(** TEST 1: Partial app applied to recursive result.
    The closure f captures tree t by [&], but must survive across the
    recursive call in the loopified version.
    f(sum_through(xs)) requires f to be stored in a continuation frame. *)
Fixpoint sum_through (l : mylist tree) : nat :=
  match l with
  | mynil => 0
  | mycons t xs =>
    let f := sum_values t in
    f (sum_through xs)
  end.

Definition test_sum_through : nat :=
  sum_through (mycons (Node Leaf 10 Leaf)
              (mycons (Node Leaf 20 Leaf)
              (mycons (Node Leaf 30 Leaf) mynil))).
(** f1(f2(f3(0))) = (10+)(20+)(30+)(0) = 60 *)

(** TEST 2: Recursive result + partial app result.
    add_through(xs) + f(0): f might be pre-evaluated or stored in frame. *)
Fixpoint add_through (l : mylist tree) : nat :=
  match l with
  | mynil => 0
  | mycons t xs =>
    let f := sum_values t in
    add_through xs + f 0
  end.

Definition test_add_through : nat :=
  add_through (mycons (Node Leaf 10 Leaf)
              (mycons (Node Leaf 20 Leaf)
              (mycons (Node Leaf 30 Leaf) mynil))).
(** 0 + 30 + 20 + 10 = 60 *)

(** TEST 3: Two partial apps from same tree, used around recursive call. *)
Fixpoint double_partial (l : mylist tree) : nat :=
  match l with
  | mynil => 0
  | mycons t xs =>
    let f := sum_values t in
    let g := sum_values t in
    f (double_partial xs) + g 0
  end.

Definition test_double_partial : nat :=
  double_partial (mycons (Node Leaf 10 Leaf)
                 (mycons (Node Leaf 20 Leaf) mynil)).
(** Inner: f2(0) = 20, g2(0) = 20. f2(double_partial []) + g2(0) = 20 + 20 = 40
    Outer: f1(40) = 50, g1(0) = 10. 50 + 10 = 60 *)

(** TEST 4: Partial app applied to recursive result, with a deeper tree. *)
Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

Fixpoint weighted_sum (l : mylist tree) (w : nat) : nat :=
  match l with
  | mynil => 0
  | mycons t xs =>
    let f := sum_values t in
    f w + weighted_sum xs (f 0)
  end.

Definition test_weighted_sum : nat :=
  weighted_sum (mycons (Node Leaf 10 Leaf)
               (mycons (Node Leaf 20 Leaf)
               (mycons (Node Leaf 30 Leaf) mynil))) 5.
(** Step 1: f1 = (10+), f1(5) = 15, weighted_sum rest (f1(0)) = weighted_sum rest 10
    Step 2: f2 = (20+), f2(10) = 30, weighted_sum rest (f2(0)) = weighted_sum rest 20
    Step 3: f3 = (30+), f3(20) = 50, weighted_sum rest (f3(0)) = weighted_sum rest 30
    Step 4: mynil -> 0
    Total: 15 + 30 + 50 + 0 = 95 *)

(** TEST 5: Map building new trees from partial app results across recursion. *)
Fixpoint transform_list (l : mylist tree) : mylist nat :=
  match l with
  | mynil => mynil
  | mycons t xs =>
    let f := sum_values t in
    mycons (f 0) (transform_list xs)
  end.

Fixpoint mysum (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x xs => x + mysum xs
  end.

Definition test_transform : nat :=
  mysum (transform_list (mycons (Node Leaf 10 Leaf)
                        (mycons (Node Leaf 20 Leaf)
                        (mycons (Node Leaf 30 Leaf) mynil)))).
(** [10, 20, 30] -> sum = 60 *)

(** TEST 6: Recursive function where partial app is used as argument
    to a higher-order function alongside the recursive call. *)
Definition apply_to (f : nat -> nat) (x : nat) : nat := f x.

Fixpoint process_list (l : mylist tree) : nat :=
  match l with
  | mynil => 0
  | mycons t xs =>
    let f := sum_values t in
    apply_to f (process_list xs)
  end.

Definition test_process_list : nat :=
  process_list (mycons (Node Leaf 10 Leaf)
               (mycons (Node Leaf 20 Leaf)
               (mycons (Node Leaf 30 Leaf) mynil))).
(** Same as sum_through: 60 *)

(** TEST 7: Nested recursion with closure capture across calls. *)
Fixpoint nested_apply (l : mylist tree) (base : nat) : nat :=
  match l with
  | mynil => base
  | mycons t xs =>
    let f := sum_values t in
    nested_apply xs (f base)
  end.

Definition test_nested_apply : nat :=
  nested_apply (mycons (Node Leaf 10 Leaf)
               (mycons (Node Leaf 20 Leaf)
               (mycons (Node Leaf 30 Leaf) mynil))) 0.
(** f1(0) = 10, f2(10) = 30, f3(30) = 60. Result = 60 *)

End MemSafetyProbe4.

Crane Extraction "mem_safety_probe4" MemSafetyProbe4.
