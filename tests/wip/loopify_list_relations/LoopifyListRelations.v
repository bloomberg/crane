From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Bool.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyListRelations.

(* List comparison and relation operations *)

(* Check if one list is prefix of another *)
Fixpoint is_prefix_of (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys => (x =? y) && is_prefix_of xs ys
  end.

(* Check if one list is suffix of another *)
Fixpoint is_suffix_of (l1 l2 : list nat) : bool :=
  let len1 := length l1 in
  let len2 := length l2 in
  if len2 <? len1 then false
  else
    let diff := len2 - len1 in
    let suffix := (fix drop n xs :=
      match n, xs with
      | 0, _ => xs
      | S n', _ :: ys => drop n' ys
      | _, [] => []
      end) diff l2 in
    (fix eq a b :=
      match a, b with
      | [], [] => true
      | x :: xs, y :: ys => if x =? y then eq xs ys else false
      | _, _ => false
      end) l1 suffix.

(* Check if one list is infix of another *)
Fixpoint is_infix_of_aux (needle haystack : list nat) : bool :=
  match haystack with
  | [] => (fix is_empty xs := match xs with [] => true | _ => false end) needle
  | _ :: ys =>
    if is_prefix_of needle haystack then true
    else is_infix_of_aux needle ys
  end.

Definition is_infix_of (needle haystack : list nat) : bool :=
  is_infix_of_aux needle haystack.

(* Find all occurrences of sublist *)
Fixpoint find_sublists_aux (needle haystack : list nat) (idx : nat) : list nat :=
  match haystack with
  | [] => []
  | _ :: ys =>
    if is_prefix_of needle haystack then
      idx :: find_sublists_aux needle ys (idx + 1)
    else
      find_sublists_aux needle ys (idx + 1)
  end.

Definition find_sublists (needle haystack : list nat) : list nat :=
  find_sublists_aux needle haystack 0.

(* List equality *)
Fixpoint list_eq (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => (x =? y) && list_eq xs ys
  | _, _ => false
  end.

(* Compare lists element-wise *)
Fixpoint list_compare (l1 l2 : list nat) : nat :=
  match l1, l2 with
  | [], [] => 0  (* equal *)
  | [], _ => 1   (* l1 < l2 *)
  | _, [] => 2   (* l1 > l2 *)
  | x :: xs, y :: ys =>
    if x <? y then 1
    else if y <? x then 2
    else list_compare xs ys
  end.

(* Zip two lists *)
Fixpoint zip (l1 l2 : list nat) : list (nat * nat) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  end.

(* Zip3 - zip three lists *)
Fixpoint zip3 (l1 l2 l3 : list nat) : list (nat * nat * nat) :=
  match l1, l2, l3 with
  | x :: xs, y :: ys, z :: zs => (x, y, z) :: zip3 xs ys zs
  | _, _, _ => []
  end.

(* Interleave two lists *)
Fixpoint interleave (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | x :: xs, y :: ys => x :: y :: interleave xs ys
  end.

(* Merge two sorted lists *)
Fixpoint merge_fuel (fuel : nat) (l1 l2 : list nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x :: xs, y :: ys =>
      if x <=? y then x :: merge_fuel fuel' xs l2
      else y :: merge_fuel fuel' l1 ys
    end
  end.

Definition merge (l1 l2 : list nat) : list nat :=
  let len1 := length l1 in
  let len2 := length l2 in
  merge_fuel (len1 + len2) l1 l2.

(* Union of two lists (no duplicates) *)
Fixpoint union (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => l2
  | x :: xs =>
    if (fix member y ys :=
      match ys with
      | [] => false
      | z :: zs => (y =? z) || member y zs
      end) x l2
    then union xs l2
    else x :: union xs l2
  end.

(* Intersection of two lists *)
Fixpoint intersection (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => []
  | x :: xs =>
    if (fix member y ys :=
      match ys with
      | [] => false
      | z :: zs => (y =? z) || member y zs
      end) x l2
    then x :: intersection xs l2
    else intersection xs l2
  end.

End LoopifyListRelations.

Set Crane Loopify.
Crane Extraction "loopify_list_relations" LoopifyListRelations.
