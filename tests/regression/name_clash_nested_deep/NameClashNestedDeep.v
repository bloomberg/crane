From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module NameClashNestedDeep.

(** Deep nesting of pattern matches to stress name generation.
    Each level creates d_a0, d_a00, d_a01, etc. *)

Inductive mylist : Type :=
| MyNil : mylist
| MyCons : nat -> mylist -> mylist.

(** Four levels of nested matching. *)
Definition deep4 (a b c d : mylist) : nat :=
  match a with
  | MyNil => 0
  | MyCons x rest_a =>
    match b with
    | MyNil => x
    | MyCons y rest_b =>
      match c with
      | MyNil => x + y
      | MyCons z rest_c =>
        match d with
        | MyNil => x + y + z
        | MyCons w rest_d => x + y + z + w
        end
      end
    end
  end.

(** Match in a let, then match on the let result. *)
Definition let_match_chain (xs ys : mylist) : nat :=
  let hd_x := match xs with MyNil => 0 | MyCons h _ => h end in
  let hd_y := match ys with MyNil => 0 | MyCons h _ => h end in
  let combined := MyCons (hd_x + hd_y) MyNil in
  match combined with
  | MyNil => 0
  | MyCons total _ => total
  end.

(** Matching where the same list is matched multiple times. *)
Definition multi_match_same (xs : mylist) : nat :=
  let first := match xs with MyNil => 0 | MyCons h _ => h end in
  let tail := match xs with MyNil => MyNil | MyCons _ t => t end in
  let second := match tail with MyNil => 0 | MyCons h _ => h end in
  first + second.

(** Nested match where inner match scrutinee is a field from outer match. *)
Definition nested_field_match (xs : mylist) : nat :=
  match xs with
  | MyNil => 0
  | MyCons _ tail =>
    match tail with
    | MyNil => 1
    | MyCons _ tail2 =>
      match tail2 with
      | MyNil => 2
      | MyCons v _ => v
      end
    end
  end.

End NameClashNestedDeep.

Crane Extraction "name_clash_nested_deep" NameClashNestedDeep.
