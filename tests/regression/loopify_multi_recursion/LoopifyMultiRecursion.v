From Stdlib Require Import Nat.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyMultiRecursion.

(* Mixed arithmetic: combines results from 3 previous calls *)
Fixpoint mixed_arith_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | 0 => 1
  | S fuel' =>
    if n <=? 0 then 1
    else if n =? 1 then 1
    else if n =? 2 then 1
    else mixed_arith_fuel fuel' (n - 1) * mixed_arith_fuel fuel' (n - 2) +
         mixed_arith_fuel fuel' (n - 3)
  end.

Definition mixed_arith (n : nat) : nat :=
  mixed_arith_fuel (n * 3) n.

(* Boolean chain: multiple || connected recursive calls *)
Fixpoint bool_or_chain_fuel (fuel : nat) (n target : nat) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    if n <=? 0 then false
    else (n =? target) || bool_or_chain_fuel fuel' (n - 1) target ||
         bool_or_chain_fuel fuel' (n - 2) target
  end.

Definition bool_or_chain (n target : nat) : nat :=
  if bool_or_chain_fuel (n * 2) n target then 1 else 0.

(* Boolean chain: multiple && connected recursive calls *)
Fixpoint bool_and_chain_fuel (fuel : nat) (n : nat) : bool :=
  match fuel with
  | 0 => true
  | S fuel' =>
    if n <=? 2 then true
    else bool_and_chain_fuel fuel' (n - 1) && bool_and_chain_fuel fuel' (n - 2)
  end.

Definition bool_and_chain (n : nat) : nat :=
  if bool_and_chain_fuel (n * 2) n then 1 else 0.

(* Quadruple recursion on four children *)
Inductive quadtree : Type :=
  | QLeaf : nat -> quadtree
  | QQuad : quadtree -> quadtree -> quadtree -> quadtree -> quadtree.

Fixpoint quad_count_leaves (t : quadtree) : nat :=
  match t with
  | QLeaf _ => 1
  | QQuad nw ne sw se =>
    quad_count_leaves nw + quad_count_leaves ne +
    quad_count_leaves sw + quad_count_leaves se
  end.

Fixpoint quad_depth (t : quadtree) : nat :=
  match t with
  | QLeaf _ => 0
  | QQuad nw ne sw se =>
    1 + max (max (quad_depth nw) (quad_depth ne))
            (max (quad_depth sw) (quad_depth se))
  end.

(* Multi-way recursion with complex control flow *)
Fixpoint hofstadter_q_fuel (fuel : nat) (n : nat) : nat :=
  match fuel with
  | 0 => 1
  | S fuel' =>
    if n <=? 0 then 0
    else if n =? 1 then 1
    else if n =? 2 then 1
    else
      let q1 := hofstadter_q_fuel fuel' (n - 1) in
      let q2 := hofstadter_q_fuel fuel' (n - 2) in
      hofstadter_q_fuel fuel' (n - q1) + hofstadter_q_fuel fuel' (n - q2)
  end.

Definition hofstadter_q (n : nat) : nat :=
  hofstadter_q_fuel (n * n + 1) n.

End LoopifyMultiRecursion.

Set Crane Loopify.
Crane Extraction "loopify_multi_recursion" LoopifyMultiRecursion.
