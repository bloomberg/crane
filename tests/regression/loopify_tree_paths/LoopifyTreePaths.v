From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyTreePaths.

Inductive tree : Type :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.

(* Helper to append element to all lists in a list of lists *)
Fixpoint map_cons (x : nat) (ll : list (list nat)) : list (list nat) :=
  match ll with
  | [] => []
  | l :: rest => (x :: l) :: map_cons x rest
  end.

(* All root-to-leaf paths in a tree *)
Fixpoint paths (t : tree) : list (list nat) :=
  match t with
  | Leaf => [[]]
  | Node l x r =>
    map_cons x (paths l) ++ map_cons x (paths r)
  end.

(* Check if any leaf satisfies a predicate via || chain *)
Inductive bool_tree : Type :=
  | BLeaf : nat -> bool_tree
  | BNode : bool_tree -> bool_tree -> bool_tree.

Fixpoint or_search (p : nat -> bool) (t : bool_tree) : bool :=
  match t with
  | BLeaf x => p x
  | BNode l r => or_search p l || or_search p r
  end.

(* Check if all leaves satisfy a predicate via && chain *)
Fixpoint and_search (p : nat -> bool) (t : bool_tree) : bool :=
  match t with
  | BLeaf x => p x
  | BNode l r => and_search p l && and_search p r
  end.

(* Count paths that sum to a target value *)
Fixpoint count_paths_sum_aux (acc : nat) (target : nat) (t : tree) : nat :=
  match t with
  | Leaf => if acc =? target then 1 else 0
  | Node l x r =>
    let new_acc := acc + x in
    count_paths_sum_aux new_acc target l + count_paths_sum_aux new_acc target r
  end.

Definition count_paths_sum (target : nat) (t : tree) : nat :=
  count_paths_sum_aux 0 target t.

(* Find leftmost path that sums to target *)
Fixpoint find_path_sum (acc : nat) (target : nat) (t : tree) : option (list nat) :=
  match t with
  | Leaf => if acc =? target then Some [] else None
  | Node l x r =>
    let new_acc := acc + x in
    match find_path_sum new_acc target l with
    | Some path => Some (x :: path)
    | None =>
      match find_path_sum new_acc target r with
      | Some path => Some (x :: path)
      | None => None
      end
    end
  end.

(* Maximum path sum *)
Fixpoint max_path_sum (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l x r =>
    x + max (max_path_sum l) (max_path_sum r)
  end.

(* All values along all paths *)
Fixpoint flatten_paths (t : tree) : list nat :=
  match t with
  | Leaf => []
  | Node l x r => x :: (flatten_paths l ++ flatten_paths r)
  end.

End LoopifyTreePaths.

Set Crane Loopify.
Crane Extraction "loopify_tree_paths" LoopifyTreePaths.
