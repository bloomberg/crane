From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyAdvancedPatterns.

(* Advanced pattern matching constructs *)

(* As-pattern with guard *)
Fixpoint len_impl (l : list nat) : nat :=
  match l with
  | [] => 0
  | _ :: xs => 1 + len_impl xs
  end.

Fixpoint as_guard (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    if 3 <? len_impl l then x :: as_guard xs
    else as_guard xs
  end.

(* Multiple guards in sequence *)
Fixpoint multi_guard (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs =>
    if 10 <? x then x + multi_guard xs
    else if 0 <? x then multi_guard xs
    else 1 + multi_guard xs
  end.

(* Four-element destructuring *)
Fixpoint four_elem (l : list nat) : nat :=
  match l with
  | [] => 0
  | [_] => 1
  | [_; _] => 2
  | [_; _; _] => 3
  | a :: b :: c :: d :: rest => a + b + c + d + four_elem rest
  end.

(* Nested tuple pattern *)
Fixpoint nested_pattern (l : list (nat * nat * nat)) : nat :=
  match l with
  | [] => 0
  | (a, b, c) :: rest => a + b + c + nested_pattern rest
  end.

(* Guard with accumulator *)
Fixpoint guard_accum (acc : nat) (l : list nat) : nat :=
  match l with
  | [] => acc
  | x :: xs =>
    if 100 <? x then guard_accum (acc * 2) xs
    else if 50 <? x then guard_accum (acc + x) xs
    else if 0 <? x then guard_accum (acc + 1) xs
    else guard_accum acc xs
  end.

(* Cons with computed value *)
Fixpoint cons_computed (n : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    let next_n := if 0 <? n then n - 1 else n in
    x :: cons_computed next_n xs
  end.

(* Or-pattern simulation with same-shape types *)
Inductive shape : Type :=
  | Circle : nat -> shape
  | Square : nat -> shape
  | Triangle : nat -> shape.

Fixpoint extract_value (s : shape) : nat :=
  match s with
  | Circle x => x
  | Square x => x
  | Triangle x => x
  end.

Fixpoint sum_shapes (l : list shape) : nat :=
  match l with
  | [] => 0
  | s :: rest => extract_value s + sum_shapes rest
  end.

(* Count by shape type *)
Fixpoint count_by_shape (l : list shape) : nat * nat * nat :=
  match l with
  | [] => (0, 0, 0)
  | s :: rest =>
    let '(circles, squares, triangles) := count_by_shape rest in
    match s with
    | Circle _ => (circles + 1, squares, triangles)
    | Square _ => (circles, squares + 1, triangles)
    | Triangle _ => (circles, squares, triangles + 1)
    end
  end.

(* Replace element at index *)
Fixpoint replace_at (idx : nat) (value : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    if idx =? 0 then value :: xs
    else x :: replace_at (idx - 1) value xs
  end.

End LoopifyAdvancedPatterns.

Set Crane Loopify.
Crane Extraction "loopify_advanced_patterns" LoopifyAdvancedPatterns.
