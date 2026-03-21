(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** Complex control flow and pattern matching edge cases. *)
Module LoopifyPatterns.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

(* ========== CONTROL FLOW PATTERNS ========== *)

(** [multi_let n] multiple sequential let bindings before recursion. *)
Fixpoint multi_let (n : nat) : nat :=
  match n with
  | O => O
  | S m =>
    let a := m in
    let b := Nat.mul a 2 in
    let c := Nat.add b 3 in
    Nat.add c (multi_let m)
  end.

(** [nested_if n] deeply nested if-then-else with recursion at different depths. *)
Fixpoint nested_if_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | O => O
  | S f =>
    match n with
    | O => O
    | S O => 1
    | S (S m as n') =>
      if Nat.eqb (Nat.modulo n' 2) O then
        (if Nat.ltb 10 n' then nested_if_fuel f (Nat.div n' 2) else nested_if_fuel f m)
      else nested_if_fuel f (if Nat.eqb m O then O else Nat.sub m 1)
    end
  end.

Definition nested_if (n : nat) : nat :=
  nested_if_fuel 1000 n.

(** [deep_nest n] deeply nested function application. *)
Fixpoint deep_nest (n : nat) : nat :=
  match n with
  | O => O
  | S m => Nat.add 1 (Nat.add 1 (Nat.add 1 (deep_nest m)))
  end.

(* ========== BOOLEAN & COMPARISON PATTERNS ========== *)

(** [bool_chain n target] multiple recursive calls in || chain. *)
Fixpoint bool_chain_fuel (fuel : nat) (n target : nat) : bool :=
  match fuel with
  | O => false
  | S f =>
    if Nat.eqb n O then false
    else
      if Nat.eqb n target then true
      else
        if Nat.eqb n 1 then false
        else
          orb (bool_chain_fuel f (Nat.sub n 1) target)
              (bool_chain_fuel f (Nat.sub n 2) target)
  end.

Definition bool_chain (n target : nat) : bool :=
  bool_chain_fuel 1000 n target.

(** [chained_comp n] boolean result with double recursion. *)
Fixpoint chained_comp (n : nat) : bool :=
  match n with
  | O => true
  | S O => true
  | S (S m as n') =>
    andb (chained_comp n') (chained_comp m)
  end.

(* ========== TUPLE & MULTIPLE ACCUMULATOR PATTERNS ========== *)

(** [tuple_constr n] recursive calls in multiple tuple positions. *)
Fixpoint tuple_constr (n : nat) : nat * nat * nat :=
  match n with
  | O => (O, O, O)
  | S m =>
    let '(a, b, c) := tuple_constr m in
    (S a, Nat.add b n, Nat.add c (Nat.mul n n))
  end.

(** [sum_prod_count l a_sum a_prod a_count] multiple accumulator updates. *)
Fixpoint sum_prod_count (l : list nat) (a_sum a_prod a_count : nat) : nat * nat * nat :=
  match l with
  | nil => (a_sum, a_prod, a_count)
  | cons x xs =>
    sum_prod_count xs (Nat.add a_sum x) (Nat.mul a_prod x) (S a_count)
  end.

(** [split_by_sign l pos neg] partition with dual accumulators. *)
Fixpoint split_by_sign_aux (l : list nat) (base : nat) (pos neg : list nat) : list nat * list nat :=
  match l with
  | nil => (pos, neg)
  | cons x xs =>
    if Nat.leb base x
    then split_by_sign_aux xs base (cons x pos) neg
    else split_by_sign_aux xs base pos (cons x neg)
  end.

Definition split_by_sign (l : list nat) (base : nat) : list nat * list nat :=
  split_by_sign_aux l base nil nil.

(* ========== GUARD PATTERNS ========== *)

(** [guard_accum acc l] multiple when-style guards with different logic. *)
Fixpoint guard_accum (acc : nat) (l : list nat) : nat :=
  match l with
  | nil => acc
  | cons x xs =>
    if Nat.ltb 100 x then guard_accum (Nat.mul acc 2) xs
    else if Nat.ltb 50 x then guard_accum (Nat.add acc x) xs
    else if Nat.ltb O x then guard_accum (S acc) xs
    else guard_accum acc xs
  end.

(** [cons_computed n l] cons with conditional parameter change. *)
Fixpoint cons_computed (n : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    let next_n := if Nat.ltb O n then Nat.sub n 1 else n in
    cons x (cons_computed next_n xs)
  end.

(* ========== COMPUTATION PATTERNS ========== *)

(** [mod_pattern n] recursive call in mod expression. *)
Fixpoint mod_pattern (n : nat) : nat :=
  match n with
  | O => 1
  | S O => 1
  | S (S m as n') =>
    Nat.modulo n' (S (mod_pattern m))
  end.

(** [alternating_ops n] alternating operations based on modulo. *)
Fixpoint alternating_ops (n : nat) : nat :=
  match n with
  | O => O
  | S m =>
    if Nat.eqb (Nat.modulo n 2) O
    then Nat.add n (alternating_ops m)
    else Nat.add (Nat.mul n 2) (alternating_ops m)
  end.

(** [max_by f l] recursive max with function application. *)
Fixpoint max_by (f : nat -> nat) (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x nil => f x
  | cons x xs =>
    let rest_max := max_by f xs in
    let fx := f x in
    if Nat.ltb fx rest_max then rest_max else fx
  end.

(** [replace_at idx value l] replace element at index. *)
Fixpoint replace_at (idx : nat) (value : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    match idx with
    | O => cons value xs
    | S i => cons x (replace_at i value xs)
    end
  end.

(* ========== LIST PATTERN MATCHING ========== *)

(** [nested_pattern l] three-element tuple pattern. *)
Fixpoint nested_pattern (l : list (nat * nat * nat)) : nat :=
  match l with
  | nil => O
  | cons (a, b, c) rest =>
    Nat.add a (Nat.add b (Nat.add c (nested_pattern rest)))
  end.

(** [let_nested n] let with nested let in binding. *)
Fixpoint let_nested (n : nat) : nat :=
  match n with
  | O => O
  | S m =>
    let a := (let b := m in S b) in
    Nat.add a (let_nested m)
  end.

(** [insert_everywhere x l] insert element at all possible positions. *)
Fixpoint insert_everywhere {A : Type} (x : A) (l : list A) : list (list A) :=
  match l with
  | nil => cons (cons x nil) nil
  | cons h t =>
    let fix map_cons_h lsts :=
      match lsts with
      | nil => nil
      | cons lst rest => cons (cons h lst) (map_cons_h rest)
      end
    in
    cons (cons x (cons h t)) (map_cons_h (insert_everywhere x t))
  end.

(** Helper: list length. *)
Fixpoint list_len (l : list nat) : nat :=
  match l with
  | nil => O
  | cons _ xs => S (list_len xs)
  end.

(** [merge_by cmp l1 l2] merge with custom comparator. *)
Fixpoint merge_by_fuel (fuel : nat) (cmp : nat -> nat -> nat) (l1 l2 : list nat) : list nat :=
  match fuel with
  | O => l1
  | S f =>
    match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | cons x xs, cons y ys =>
      if Nat.leb (cmp x y) O
      then cons x (merge_by_fuel f cmp xs l2)
      else cons y (merge_by_fuel f cmp l1 ys)
    end
  end.

Definition merge_by (cmp : nat -> nat -> nat) (l1 l2 : list nat) : list nat :=
  merge_by_fuel (Nat.add (list_len l1) (list_len l2)) cmp l1 l2.

(* ========== DOUBLE RECURSION PATTERNS ========== *)

(** [process_twice l] applies recursion twice: process(process(xs)). *)
Fixpoint process_twice_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons x xs =>
      let first := process_twice_fuel f xs in
      let second := process_twice_fuel f first in
      cons x second
    end
  end.

Definition process_twice (l : list nat) : list nat :=
  process_twice_fuel 100 l.

(** [as_guard l] uses as-pattern with guard (length check). *)
Fixpoint as_guard_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons x xs =>
      let all := cons x xs in
      if Nat.ltb 3 (list_len all)
      then cons x (as_guard_fuel f xs)
      else as_guard_fuel f xs
    end
  end.

Definition as_guard (l : list nat) : list nat :=
  as_guard_fuel 100 l.

(** [quad_sum_pattern l] pattern with 4-way split. *)
Fixpoint quad_sum_pattern (l : list nat) : nat :=
  match l with
  | nil => O
  | cons a nil => a
  | cons a (cons b nil) => Nat.add a b
  | cons a (cons b (cons c nil)) => Nat.add a (Nat.add b c)
  | cons a (cons b (cons c (cons d rest))) =>
    Nat.add (Nat.add a b) (Nat.add (Nat.add c d) (quad_sum_pattern rest))
  end.

(** [multi_guard l] demonstrates pattern with multiple conditional branches. *)
Fixpoint multi_guard (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs =>
    let rest := multi_guard xs in
    if Nat.ltb 10 x then Nat.add x rest
    else if Nat.ltb O x then rest
    else Nat.add 1 rest
  end.

(* ========== RECURSIVE RESULT REUSE PATTERNS ========== *)

(** Internal helper for double_append. *)
Fixpoint append_lists (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (append_lists xs l2)
  end.

(** [double_append l1 l2] uses recursive result twice: h :: (rest @ rest). *)
Fixpoint double_append (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => l2
  | cons h t =>
    let rest := double_append t l2 in
    cons h (append_lists rest rest)
  end.

(** [process_twice_alt l] applies transformation twice on recursive result. *)
Fixpoint process_twice_alt_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S f =>
    match l with
    | nil => nil
    | cons x xs =>
      let once := process_twice_alt_fuel f xs in
      let twice := process_twice_alt_fuel f once in
      cons x twice
    end
  end.

Definition process_twice_alt (l : list nat) : list nat :=
  process_twice_alt_fuel 100 l.

(** [sum_if_positive_else_double l] conditional logic on each element. *)
Fixpoint sum_if_positive_else_double (l : list nat) : nat :=
  match l with
  | nil => O
  | cons x xs =>
    let rest := sum_if_positive_else_double xs in
    if Nat.eqb x O then Nat.add (Nat.mul 2 x) rest
    else Nat.add x rest
  end.

(** [take_until p l] takes elements until predicate is true. *)
Fixpoint take_until (p : nat -> bool) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if p x then nil
    else cons x (take_until p xs)
  end.

(* ========== COMPLEX CONDITIONAL PATTERNS ========== *)

(** [partition_by p q l] partitions into 3 categories based on two predicates. *)
Fixpoint partition_by (p q : nat -> bool) (l : list nat) : list nat * list nat * list nat :=
  match l with
  | nil => (nil, nil, nil)
  | cons x xs =>
    let '(as_, bs, cs) := partition_by p q xs in
    if p x then (cons x as_, bs, cs)
    else if q x then (as_, cons x bs, cs)
    else (as_, bs, cons x cs)
  end.

(** [merge_alternating l1 l2] merges two lists by alternating elements. *)
Fixpoint merge_alternating (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | cons x xs, cons y ys => cons x (cons y (merge_alternating xs ys))
  end.

(** [filter_map_indexed p f l] filters and maps with index. *)
Fixpoint filter_map_indexed_aux (p : nat -> nat -> bool) (f : nat -> nat) (l : list nat) (idx : nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if p idx x
    then cons (f x) (filter_map_indexed_aux p f xs (S idx))
    else filter_map_indexed_aux p f xs (S idx)
  end.

Definition filter_map_indexed (p : nat -> nat -> bool) (f : nat -> nat) (l : list nat) : list nat :=
  filter_map_indexed_aux p f l O.

(** [four_elem l] four-element destructuring pattern with fallback cases. *)
Fixpoint four_elem (l : list nat) : nat :=
  match l with
  | nil => O
  | cons _ nil => 1
  | cons _ (cons _ nil) => 2
  | cons _ (cons _ (cons _ nil)) => 3
  | cons a (cons b (cons c (cons d rest))) =>
    Nat.add a (Nat.add b (Nat.add c (Nat.add d (four_elem rest))))
  end.

End LoopifyPatterns.

Set Crane Loopify.
Crane Extraction "loopify_patterns" LoopifyPatterns.
