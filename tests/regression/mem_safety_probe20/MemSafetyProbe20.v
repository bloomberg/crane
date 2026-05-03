From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module MemSafetyProbe20.

(** Probe 20: Closures wrapped in data structures + if/match return.

    Attack vector: return_captures_by_value (translation.ml:1220-1227)
    only processes top-level Sreturn statements. If we wrap closures
    inside a data structure (preventing uncurrying) and return them
    from inside an if/match, the outer List.map matches [s -> s]
    and the lambdas remain [&], creating dangling references. *)

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint tree_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l v r => tree_sum l + v + tree_sum r
  end.

(** Wrapper type: wraps a closure in a data structure to prevent
    the function from being fully uncurried. *)
Inductive wrapped : Type :=
| Wrap : (nat -> nat) -> wrapped.

Definition unwrap (w : wrapped) (x : nat) : nat :=
  match w with
  | Wrap f => f x
  end.

(** TEST 1: Return wrapped closure from if-branch.
    The if becomes top-level Sif. return_captures_by_value sees
    Sif, matches [s -> s], leaves lambda as [&]. *)
Definition wrap_if (t : tree) (b : bool) : wrapped :=
  if b then Wrap (fun n => tree_sum t + n)
  else Wrap (fun n => n).

Definition test_wrap_if : nat :=
  let w := wrap_if (Node Leaf 42 Leaf) true in
  unwrap w 0.
(** tree_sum = 42. unwrap (Wrap (fun n => 42+n)) 0 = 42 *)

(** TEST 2: Return wrapped closure from match on custom type. *)
Inductive choice : Type :=
| CLeft : choice
| CRight : choice.

Definition wrap_match (t : tree) (c : choice) : wrapped :=
  match c with
  | CLeft => Wrap (fun n => tree_sum t + n)
  | CRight => Wrap (fun n => n)
  end.

Definition test_wrap_match : nat :=
  let w := wrap_match (Node (Node Leaf 3 Leaf) 7 Leaf) CLeft in
  unwrap w 0.
(** tree_sum = 10. Result = 10 *)

(** TEST 3: Pair of closure and value, returned from if.
    Uses prod to wrap the closure. *)
Definition pair_from_if (t : tree) (b : bool) : wrapped * nat :=
  if b then (Wrap (fun n => tree_sum t + n), tree_sum t)
  else (Wrap (fun n => n), 0).

Definition test_pair_if : nat :=
  let p := pair_from_if (Node Leaf 15 Leaf) true in
  let w := fst p in
  let v := snd p in
  unwrap w v.
(** tree_sum = 15. v = 15. unwrap (Wrap (fun n => 15+n)) 15 = 30 *)

(** TEST 4: Wrapped closure captured in a locally-constructed tree.
    The let-bound tree is stack-allocated. *)
Definition wrap_local (n : nat) (b : bool) : wrapped :=
  let t := Node Leaf n Leaf in
  if b then Wrap (fun m => tree_sum t + m)
  else Wrap (fun m => m).

Definition test_wrap_local : nat :=
  let w := wrap_local 20 true in
  unwrap w 5.
(** t = Node Leaf 20 Leaf, tree_sum = 20. Result = 25 *)

(** TEST 5: Double use of unwrapped closure. *)
Definition test_double_unwrap : nat :=
  let w := wrap_if (Node Leaf 7 Leaf) true in
  unwrap w 1 + unwrap w 2.
(** unwrap w 1 = 8, unwrap w 2 = 9. Total = 17 *)

(** TEST 6: Nested wrapped closure: wrapped inside a pair inside if. *)
Definition nested_wrap (t : tree) (b1 b2 : bool) : wrapped :=
  if b1
  then (if b2
        then Wrap (fun n => tree_sum t + n)
        else Wrap (fun n => tree_sum t * 2 + n))
  else Wrap (fun n => n).

Definition test_nested_wrap : nat :=
  let w := nested_wrap (Node Leaf 5 Leaf) true false in
  unwrap w 0.
(** tree_sum = 5. 5 * 2 + 0 = 10 *)

(** TEST 7: List of wrapped closures from if branches. *)
Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Definition wrap_list (t : tree) (b : bool) : mylist wrapped :=
  if b
  then mycons (Wrap (fun n => tree_sum t + n))
              (mycons (Wrap (fun n => tree_sum t + tree_sum t + n)) mynil)
  else mycons (Wrap (fun n => n)) mynil.

Fixpoint sum_wrapped (l : mylist wrapped) (x : nat) : nat :=
  match l with
  | mynil => 0
  | mycons w rest => unwrap w x + sum_wrapped rest x
  end.

Definition test_wrap_list : nat :=
  let l := wrap_list (Node Leaf 3 Leaf) true in
  sum_wrapped l 0.
(** unwrap (Wrap (fun n => 3+n)) 0 = 3
    unwrap (Wrap (fun n => 3+3+n)) 0 = 6
    Total = 9 *)

End MemSafetyProbe20.

Crane Extraction "mem_safety_probe20" MemSafetyProbe20.
