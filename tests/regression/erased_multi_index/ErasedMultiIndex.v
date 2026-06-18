From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

(** Memory safety probe: type-indexed inductives with multiple indices.

    Tests code generation for inductives indexed by multiple types.
    These should all be erased to std::any, and any_cast must use
    the correct type. *)

Module ErasedMultiIndex.

(** Two type indices — both erased *)
Inductive tagged : Set -> Set -> Type :=
  | MkTagged : forall (K V : Set), K -> V -> tagged K V.

Definition get_key {K V : Set} (t : tagged K V) : K :=
  match t with
  | MkTagged _ _ k _ => k
  end.

Definition get_val {K V : Set} (t : tagged K V) : V :=
  match t with
  | MkTagged _ _ _ v => v
  end.

Definition test_tagged : nat :=
  let t := MkTagged _ _ 42 true in
  get_key t.

(** Heterogeneous list using type-indexed existential *)
Inductive hlist : Type :=
  | HNil : hlist
  | HCons : forall (A : Set), A -> hlist -> hlist.

Fixpoint hlist_length (l : hlist) : nat :=
  match l with
  | HNil => 0
  | HCons _ _ rest => 1 + hlist_length rest
  end.

Definition test_hlist : nat :=
  let l := HCons _ 42 (HCons _ true (HCons _ 7 HNil)) in
  hlist_length l.


End ErasedMultiIndex.

Crane Extraction "erased_multi_index" ErasedMultiIndex.
