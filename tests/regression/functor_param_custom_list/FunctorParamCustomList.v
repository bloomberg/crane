From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.DequeList.
From Stdlib Require Import List Bool.
Import ListNotations.

(** A functor's parameter type inside a custom-mapped type: [R.String] is
    [list R.Sigma], and [list] is a custom.  Extraction carried the type
    argument [R.Sigma] among the custom's term arguments too, and the
    custom's conversion read it as a value -- a callee no callable plan
    exists for, an anomaly once a missing plan became one.  From ParseALot,
    whose [Matcher] parameter [R.Ty.Sigma] stopped its extraction. *)

Module FunctorParamCustomList.
  Module Type T.
    Parameter Sigma : Type.
    Parameter ok : Sigma -> bool.
    Definition String : Type := list Sigma.
  End T.

  Module Impl (R : T).
    Fixpoint all_ok (s : R.String) : bool :=
      match s with
      | [] => true
      | x :: xs => andb (R.ok x) (all_ok xs)
      end.
  End Impl.

  Module Digits <: T.
    Definition Sigma := nat.
    Definition ok (n : nat) : bool := Nat.ltb n 10.
    Definition String : Type := list Sigma.
  End Digits.

  Module DigitsImpl := Impl Digits.

  Definition all_digits (s : list nat) : bool := DigitsImpl.all_ok s.
End FunctorParamCustomList.

Crane Extraction "functor_param_custom_list" FunctorParamCustomList.
