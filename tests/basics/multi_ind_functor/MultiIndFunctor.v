(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Test: Functor defining multiple inductives that reference each other *)

From Stdlib Require Import NArith.
Open Scope nat_scope.

(* Module type for elements *)
Module Type Elem.
  Parameter t : Type.
  Parameter dflt : t.  (* 'default' is a C++ reserved keyword, use 'dflt' *)
End Elem.

(* Functor that defines multiple inductives *)
Module Container (E : Elem).
  (* First inductive: a simple option-like type using nat to avoid E.t in recursors *)
  Inductive maybe : Type :=
  | Nothing : maybe
  | Just : nat -> maybe.

  (* Second inductive: a list that uses the first inductive *)
  Inductive mlist : Type :=
  | MNil : mlist
  | MCons : maybe -> mlist -> mlist.

  (* Third inductive: a tree using the list *)
  Inductive mtree : Type :=
  | Leaf : maybe -> mtree
  | Node : mlist -> mtree.  (* children stored in mlist *)

  (* Functions operating on these types *)
  Definition is_nothing (m : maybe) : bool :=
    match m with
    | Nothing => true
    | Just _ => false
    end.

  Fixpoint mlist_length (l : mlist) : nat :=
    match l with
    | MNil => 0
    | MCons _ rest => S (mlist_length rest)
    end.

  Definition tree_size (t : mtree) : nat :=
    match t with
    | Leaf m => if is_nothing m then 0 else 1
    | Node children => mlist_length children
    end.

  (* Values using the inductives *)
  Definition empty_maybe : maybe := Nothing.
  Definition some_val : maybe := Just 42.
  Definition sample_list : mlist := MCons (Just 42) (MCons Nothing MNil).
  Definition sample_tree : mtree := Node sample_list.
End Container.

(* Concrete element module *)
Module NatElem : Elem.
  Definition t := nat.
  Definition dflt := 42.
End NatElem.

(* Instantiate the functor *)
Module NatContainer := Container NatElem.

(* Test values *)
Definition test_is_nothing := NatContainer.is_nothing NatContainer.empty_maybe.
Definition test_list_len := NatContainer.mlist_length NatContainer.sample_list.
Definition test_tree_size := NatContainer.tree_size NatContainer.sample_tree.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Require Crane.Mapping.NatIntStd.

Crane Extraction "multi_ind_functor" test_is_nothing test_list_len test_tree_size.
