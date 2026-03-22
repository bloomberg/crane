From Stdlib Require Import Nat.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyNestedConstructs.

(* Nested control flow and let constructs *)

(* Multiple sequential let bindings *)
Fixpoint multi_let (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    let a := n' in
    let b := a * 2 in
    let c := b + 3 in
    c + multi_let a
  end.

(* Deeply nested if-then-else *)
Fixpoint nested_if_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    if n <=? 0 then 0
    else if n =? 1 then 1
    else if n mod 2 =? 0 then
      (if 10 <? n then nested_if_fuel fuel' (n / 2)
       else nested_if_fuel fuel' (n - 1))
    else nested_if_fuel fuel' (n - 2)
  end.

Definition nested_if (n : nat) : nat :=
  nested_if_fuel n n.

(* Deep nesting of function applications *)
Fixpoint deep_nest (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    let inner := deep_nest n' in
    let mid := inner + 1 in
    mid * 2
  end.

(* Let with nested let in binding *)
Fixpoint let_nested (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    let a := (let b := n' in b + 1) in
    a + let_nested n'
  end.

(* Modulo with recursive divisor *)
Fixpoint mod_pattern_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | 0 => 1
  | S fuel' =>
    if n <=? 1 then 1
    else n mod (1 + mod_pattern_fuel fuel' (n - 1))
  end.

Definition mod_pattern (n : nat) : nat :=
  mod_pattern_fuel n n.

(* Tuple construction with recursive calls *)
Fixpoint tuple_constr (n : nat) : nat * nat * nat :=
  match n with
  | 0 => (0, 0, 0)
  | S n' =>
    let '(a, b, c) := tuple_constr n' in
    (a + 1, b + n, c + n * n)
  end.

(* Alternating operations based on modulo *)
Fixpoint alternating_ops (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    if n mod 2 =? 0 then
      n + alternating_ops n'
    else
      n * 2 + alternating_ops n'
  end.

(* Chained boolean operations *)
Fixpoint chained_comp_fuel (fuel : nat) (n : nat) : bool :=
  match fuel with
  | 0 => true
  | S fuel' =>
    if n <=? 2 then true
    else chained_comp_fuel fuel' (n - 1) && chained_comp_fuel fuel' (n - 2)
  end.

Definition chained_comp (n : nat) : nat :=
  if chained_comp_fuel (n * 2) n then 1 else 0.

(* Let binding with complex expression *)
Fixpoint compute_with_lets (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' =>
      let x := compute_with_lets n' in
      let y := compute_with_lets n'' in
      let z := x + y in
      z * 2
    end
  end.

(* Nested match with recursion at different levels *)
Fixpoint nested_match (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => n + nested_match n''
    end
  end.

End LoopifyNestedConstructs.

Set Crane Loopify.
Crane Extraction "loopify_nested_constructs" LoopifyNestedConstructs.
