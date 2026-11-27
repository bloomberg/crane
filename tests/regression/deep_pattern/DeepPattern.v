(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   Try to create deep nested patterns that might not optimize well,
   potentially triggering the Impossible exception or creating unusual patterns.
*)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module DeepPattern.

(* Nested inductive types *)
Inductive tree : Type :=
| Leaf : nat -> tree
| Node : tree -> tree -> tree.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

(* Deeply nested pattern matching *)
Definition deep_match (t : tree) : nat :=
  match t with
  | Leaf n => n
  | Node (Leaf a) (Leaf b) => a + b
  | Node (Leaf a) (Node (Leaf b) (Leaf c)) => a + b + c
  | Node (Node (Leaf a) (Leaf b)) (Leaf c) => a + b + c
  | Node (Node (Leaf a) (Leaf b)) (Node (Leaf c) (Leaf d)) => a + b + c + d
  | Node (Node (Node (Leaf a) (Leaf b)) (Leaf c)) (Leaf d) => a + b + c + d
  | _ => 0
  end.

(* Pattern with multiple constructors at same level *)
Definition multi_constructor (t1 t2 : tree) : nat :=
  match t1, t2 with
  | Leaf a, Leaf b => a + b
  | Node (Leaf a) _, Leaf b => a + b
  | Leaf a, Node (Leaf b) _ => a + b
  | Node (Leaf a) (Leaf b), Node (Leaf c) (Leaf d) => a + b + c + d
  | _, _ => 0
  end.

(* Match on list with deep patterns *)
Definition list_deep_match (l : list tree) : nat :=
  match l with
  | nil => 0
  | cons (Leaf n) nil => n
  | cons (Leaf a) (cons (Leaf b) nil) => a + b
  | cons (Node (Leaf a) (Leaf b)) (cons (Leaf c) nil) => a + b + c
  | cons (Node (Leaf a) (Leaf b)) (cons (Node (Leaf c) (Leaf d)) nil) => a + b + c + d
  | _ => 0
  end.

(* Wildcard pattern with bound variables (Pwild with non-empty ids?) *)
Definition wildcard_with_bindings (t : tree) : nat :=
  match t with
  | Leaf n => n
  | Node l r =>
      (* Inner match might create unusual patterns *)
      let x := match l with Leaf a => a | _ => 0 end in
      let y := match r with Leaf b => b | _ => 0 end in
      x + y
  end.

(* As-patterns (if supported) *)
Definition as_pattern_test (t : tree) : tree :=
  match t with
  | Leaf _ as orig => orig
  | Node _ _ as orig => orig
  end.

(* Guard-like conditions *)
Fixpoint has_value (t : tree) (target : nat) : bool :=
  match t with
  | Leaf n => Nat.eqb n target
  | Node l r => has_value l target || has_value r target
  end.

Definition conditional_match (t : tree) (target : nat) : nat :=
  match t with
  | Leaf n => if Nat.eqb n target then 100 else n
  | Node l r =>
      if has_value t target then 200
      else match l with Leaf a => a | _ => 0 end
  end.

(* Multiple levels of nested lets in match *)
Definition nested_let_match (t : tree) : nat :=
  match t with
  | Leaf n => n
  | Node l r =>
      let a := match l with Leaf x => x | _ => 0 end in
      let b := match r with Leaf y => y | _ => 0 end in
      let c := a + b in
      let d := c * 2 in
      let e := d + 1 in
      e
  end.

Definition test1 := deep_match (Node (Leaf 1) (Leaf 2)).
Definition test2 := multi_constructor (Leaf 5) (Leaf 10).

End DeepPattern.

Crane Extraction "deep_pattern" DeepPattern.
