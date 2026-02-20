(* Benchmark: functions that create and locally destructure inductive values *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module BenchLetIn.

Inductive pair (A B : Type) : Type :=
| Pair : A -> B -> pair A B.
Arguments Pair {A B} _ _.

(* Swap via local pair — creates pair, destructures, returns component *)
Definition swap_snd (a b : nat) : nat :=
  let p := Pair a b in
  match p with Pair _ y => y end.

(* Add via local pair *)
Definition add_via_pair (a b : nat) : nat :=
  let p := Pair a b in
  match p with Pair x y => Nat.add x y end.

(* Nested: two local pairs *)
Definition nested_swap (a b c d : nat) : nat :=
  let p1 := Pair a b in
  let p2 := Pair c d in
  match p1 with Pair x _ =>
    match p2 with Pair _ w => Nat.add x w end
  end.

(* Recursive function with local pair each iteration *)
Fixpoint sum_via_pairs (n : nat) : nat :=
  match n with
  | O => O
  | S m =>
    let p := Pair n m in
    match p with Pair x y => Nat.add x (sum_via_pairs y) end
  end.

Inductive triple (A B C : Type) : Type :=
| Triple : A -> B -> C -> triple A B C.
Arguments Triple {A B C} _ _ _.

(* Triple create and project *)
Definition mid3 (a b c : nat) : nat :=
  let t := Triple a b c in
  match t with Triple _ y _ => y end.

(* Sum all three *)
Definition sum3 (a b c : nat) : nat :=
  let t := Triple a b c in
  match t with Triple x y z => Nat.add x (Nat.add y z) end.

(* Chain: create, destructure, create again, destructure *)
Definition chain_pairs (a b c : nat) : nat :=
  let p1 := Pair a b in
  match p1 with Pair x _ =>
    let p2 := Pair x c in
    match p2 with Pair u v => Nat.add u v end
  end.

(* Correctness tests *)
Definition test_swap := swap_snd 3 4.
Definition test_add := add_via_pair 3 4.
Definition test_nested := nested_swap 1 2 3 4.
Definition test_sum_pairs := sum_via_pairs 5.
Definition test_mid3 := mid3 1 2 3.
Definition test_sum3 := sum3 1 2 3.
Definition test_chain := chain_pairs 1 2 3.

End BenchLetIn.

Crane Extraction "bench_let_in" BenchLetIn.
