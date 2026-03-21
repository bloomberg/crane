(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.
Require Crane.Extraction.

(** Nested and complex data structures. *)
Module LoopifyStructures.

(* ========== NESTED STRUCTURES ========== *)

(** Nested list: elements or nested lists. *)
Inductive nested : Type :=
| Elem : nat -> nested
| NList : list nested -> nested.

(** Helper: sum all elements in a list of nested structures.
    Handles both tree and list levels in one function for full loopification. *)
Fixpoint sum_nested_list_fuel (fuel : nat) (l : list nested) : nat :=
  match fuel with
  | O => O
  | S f =>
    match l with
    | nil => O
    | cons item rest =>
      match item with
      | Elem x => Nat.add x (sum_nested_list_fuel f rest)
      | NList lst => Nat.add (sum_nested_list_fuel f lst)
                             (sum_nested_list_fuel f rest)
      end
    end
  end.

(** [nested_sum n] sums all elements in a nested structure. *)
Definition nested_sum (n : nested) : nat :=
  match n with
  | Elem x => x
  | NList lst => sum_nested_list_fuel 1000 lst
  end.

(** Helper: compute max depth among a list of nested structures. *)
Fixpoint depth_nested_list_fuel (fuel : nat) (l : list nested) : nat :=
  match fuel with
  | O => O
  | S f =>
    match l with
    | nil => O
    | cons item rest =>
      match item with
      | Elem _ =>
        let rest_max := depth_nested_list_fuel f rest in
        if Nat.leb O rest_max then rest_max else O
      | NList lst =>
        let d := S (depth_nested_list_fuel f lst) in
        let rest_max := depth_nested_list_fuel f rest in
        if Nat.leb d rest_max then rest_max else d
      end
    end
  end.

(** [nested_depth n] computes maximum nesting depth. *)
Definition nested_depth (n : nested) : nat :=
  match n with
  | Elem _ => O
  | NList lst => S (depth_nested_list_fuel 1000 lst)
  end.

(** Helper: flatten a list of nested structures to a flat list of nats. *)
Fixpoint flatten_nested_list_fuel (fuel : nat) (l : list nested) : list nat :=
  match fuel with
  | O => nil
  | S f =>
    match l with
    | nil => nil
    | cons item rest =>
      match item with
      | Elem x => cons x (flatten_nested_list_fuel f rest)
      | NList lst => app (flatten_nested_list_fuel f lst)
                                 (flatten_nested_list_fuel f rest)
      end
    end
  end.

(** [nested_flatten n] flattens to a regular list. *)
Definition nested_flatten (n : nested) : list nat :=
  match n with
  | Elem x => cons x nil
  | NList lst => flatten_nested_list_fuel 1000 lst
  end.

(* ========== QUADTREE ========== *)

(** Quadtree: leaf or 4-way branch. *)
Inductive quadtree : Type :=
| QLeaf : nat -> quadtree
| Quad : quadtree -> quadtree -> quadtree -> quadtree -> quadtree.

(** [quad_sum t] sums all values in quadtree. *)
Fixpoint quad_sum (t : quadtree) : nat :=
  match t with
  | QLeaf x => x
  | Quad nw ne sw se =>
    Nat.add (quad_sum nw) (Nat.add (quad_sum ne)
      (Nat.add (quad_sum sw) (quad_sum se)))
  end.

(** [quad_depth t] computes quadtree depth. *)
Fixpoint quad_depth (t : quadtree) : nat :=
  match t with
  | QLeaf _ => O
  | Quad nw ne sw se =>
    let d1 := quad_depth nw in
    let d2 := quad_depth ne in
    let d3 := quad_depth sw in
    let d4 := quad_depth se in
    S (if Nat.leb (if Nat.leb d1 d2 then d2 else d1)
                   (if Nat.leb d3 d4 then d4 else d3)
       then (if Nat.leb d3 d4 then d4 else d3)
       else (if Nat.leb d1 d2 then d2 else d1))
  end.

(** [quad_map f t] applies function to all leaves. *)
Fixpoint quad_map (f : nat -> nat) (t : quadtree) : quadtree :=
  match t with
  | QLeaf x => QLeaf (f x)
  | Quad nw ne sw se =>
    Quad (quad_map f nw) (quad_map f ne) (quad_map f sw) (quad_map f se)
  end.

(* ========== OPTION TYPE RECURSION ========== *)

(** [find_opt p l] finds first element satisfying predicate, returns option. *)
Fixpoint find_opt (p : nat -> bool) (l : list nat) : option nat :=
  match l with
  | nil => None
  | cons x xs => if p x then Some x else find_opt p xs
  end.

(** [map_opt f l] maps option-returning function and filters out Nones. *)
Fixpoint map_opt (f : nat -> option nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    match f x with
    | None => map_opt f xs
    | Some y => cons y (map_opt f xs)
    end
  end.

(** [filter_map p f l] filters and maps in one pass. *)
Fixpoint filter_map (p : nat -> bool) (f : nat -> nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons x xs =>
    if p x
    then cons (f x) (filter_map p f xs)
    else filter_map p f xs
  end.

(** [find_first_some l] finds first Some value in list of options. *)
Fixpoint find_first_some (l : list (option nat)) : option nat :=
  match l with
  | nil => None
  | cons x xs =>
    match x with
    | Some v => Some v
    | None => find_first_some xs
    end
  end.

(** Tree type with values in leaves. *)
Inductive ltree : Type :=
| LLeaf : nat -> ltree
| LNode : nat -> ltree -> ltree -> ltree.

(** [ltree_max t1 t2] element-wise max of two leaf-trees. *)
Fixpoint ltree_max (t1 t2 : ltree) : ltree :=
  match t1, t2 with
  | LLeaf x, LLeaf y =>
    LLeaf (if Nat.leb x y then y else x)
  | LNode x l1 r1, LNode y l2 r2 =>
    let max_val := if Nat.leb x y then y else x in
    LNode max_val (ltree_max l1 l2) (ltree_max r1 r2)
  | LNode _ _ _, LLeaf _ => t1
  | LLeaf _, LNode _ _ _ => t2
  end.

End LoopifyStructures.

Set Crane Loopify.
Crane Extraction "loopify_structures" LoopifyStructures.
