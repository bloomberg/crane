(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [Ret] says nothing about its tree's event family, so its annotation
    leaves the family erased; the family is the one the enclosing [go] is
    built at.  Built at the erased family instead, every [Ret] of [run_exc]
    (Vellvm's exception catcher) was converted to the result's family, node
    by node, as the tree was read. *)

From Stdlib Require Import List.
From ITree Require Import ITree.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
Import ITreeNotations.

Module ItreeRetFamilyFromResult.
  Variant AE : Type -> Type := A : AE nat.
  Variant BE : Type -> Type := B : nat -> BE unit.
  Definition TopE := AE +' BE.
  Definition top (R : Type) := itree TopE R.

  Definition exc_of {X} (e : TopE X) : option nat :=
    match e with inr1 (B n) => Some n | _ => None end.

  CoFixpoint run_exc {R} (t : top R) : top (nat + R) :=
    match observe t with
    | RetF r => Ret (inr r)
    | TauF t' => Tau (run_exc t')
    | VisF e k => match exc_of e with
                  | Some n => Ret (inl n)
                  | None => Vis e (fun x => run_exc (k x))
                  end
    end.

  Definition ok : top nat := Tau (Tau (Ret 3)).
  Definition raises : top nat := Tau (Vis (inr1 (B 7)) (fun _ => Ret 0)).

  Fixpoint result (fuel : nat) (t : top (nat + nat)) : nat :=
    match fuel with
    | O => 0
    | S f => match observe t with
             | RetF (inl n) => 100 + n
             | RetF (inr n) => n
             | TauF t' => result f t'
             | VisF _ _ => 0
             end
    end.

  Definition ok_result : nat := result 10 (run_exc ok).
  Definition raises_result : nat := result 10 (run_exc raises).
End ItreeRetFamilyFromResult.

Crane Extraction "itree_ret_family_from_result" ItreeRetFamilyFromResult.
