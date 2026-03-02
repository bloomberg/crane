(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Dependent records — field types depend on earlier fields. *)

From Stdlib Require Import Nat Bool List.
Import ListNotations.

Module DepRecord.

(* === Simple dependent record: carrier + operation === *)

Record Magma := mkMagma {
  carrier : Type;
  op : carrier -> carrier -> carrier
}.

Definition nat_magma : Magma := mkMagma nat Nat.add.
Definition bool_magma : Magma := mkMagma bool andb.

(* === Algebraic structure style: carrier + op + identity === *)

Record Monoid := mkMonoid {
  m_carrier : Type;
  m_op : m_carrier -> m_carrier -> m_carrier;
  m_id : m_carrier
}.

Definition nat_monoid : Monoid := mkMonoid nat Nat.add 0.
Definition nat_mul_monoid : Monoid := mkMonoid nat Nat.mul 1.

(* === Generic fold using monoid === *)

Fixpoint mfold (M : Monoid) (l : list (m_carrier M)) : m_carrier M :=
  match l with
  | [] => m_id M
  | x :: rest => m_op M x (mfold M rest)
  end.

Definition test_fold_add : nat := mfold nat_monoid [1; 2; 3; 4].
Definition test_fold_mul : nat := mfold nat_mul_monoid [2; 3; 4].

(* === Sigma-style: type tag + payload === *)

Inductive tag : Type := TNat | TBool.

Definition tag_type (t : tag) : Type :=
  match t with
  | TNat => nat
  | TBool => bool
  end.

Record Tagged := mkTagged {
  the_tag : tag;
  the_value : tag_type the_tag
}.

Definition tagged_nat : Tagged := mkTagged TNat 42.
Definition tagged_bool : Tagged := mkTagged TBool true.

End DepRecord.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "dep_record" DepRecord.
