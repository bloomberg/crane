(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a match whose return type is computed from an index,
    [match t with TNat => nat | _ => unit], emits [return std::monostate{}]
    from a [uint64_t] function in the arm the index rules out.  The arm is
    unreachable -- [e : exp TNat] -- but its body is still generated and has
    to type-check.  With two constructors of [ty] the wildcard covers one and
    the result is right; with a third constructor carrying arguments the
    wildcard covers two and the [unit] arm is no longer erased. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module DepMatchWildcardUnitArm.

Inductive ty := TNat | TBool | TArr : ty -> ty -> ty.

Inductive exp : ty -> Type :=
| ELit : nat -> exp TNat
| EB : bool -> exp TBool
| EIf : forall t, exp t -> exp t.

Fixpoint evn (e : exp TNat) : nat :=
  match e in exp t return (match t with TNat => nat | _ => unit end) with
  | ELit n => n
  | EB _ => tt
  | EIf t x =>
      match t return exp t -> (match t with TNat => nat | _ => unit end) with
      | TNat => fun x => evn x
      | _ => fun _ => tt
      end x
  end.

Definition result : nat := evn (EIf TNat (ELit 4)).

End DepMatchWildcardUnitArm.

Crane Extraction "dep_match_wildcard_unit_arm" DepMatchWildcardUnitArm.
