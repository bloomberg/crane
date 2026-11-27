(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A pair or option of functor-abstract components, matched and its
    components handed to the components' own functions, is a borrowed
    parameter.  The components' copy cost is unknown ([A.t] may be a list),
    so the pair is lent by const reference, as an [A.t] alone is, and is not
    copied whole into the call.  A pair of components known to copy
    for free stays by value. *)

From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatInt.

Module PairAbstractComponentsByReference.

Module Type Cmp.
  Parameter t : Type.
  Parameter compare : t -> t -> comparison.
End Cmp.

Module PairCmp (A : Cmp) (B : Cmp).
  Definition t := (A.t * B.t)%type.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | (a, b), (a', b') =>
      match A.compare a a' with
      | Eq => B.compare b b'
      | c => c
      end
    end.

  Definition eqb (x y : t) : bool :=
    match compare x y with Eq => true | _ => false end.
End PairCmp.

Module OptCmp (A : Cmp).
  Definition t := option A.t.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | None, None => Eq
    | None, Some _ => Lt
    | Some _, None => Gt
    | Some a, Some a' => A.compare a a'
    end.
End OptCmp.

Module NatListCmp <: Cmp.
  Definition t := list nat.
  Fixpoint compare (x y : t) : comparison :=
    match x, y with
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    | a :: x', b :: y' =>
      match Nat.compare a b with Eq => compare x' y' | c => c end
    end.
End NatListCmp.

Module NatCmp <: Cmp.
  Definition t := nat.
  Definition compare := Nat.compare.
End NatCmp.

Module P := PairCmp NatListCmp NatCmp.
Module O := OptCmp NatListCmp.

Definition sum_pair (p : nat * nat) : nat := let (a, b) := p in a + b.

Definition test_pair : comparison := P.compare ([1; 2], 3) ([1; 2], 4).
Definition test_opt : comparison := O.compare (Some [1]) (Some [1; 0]).

End PairAbstractComponentsByReference.

Crane Extraction "pair_abstract_components_by_reference" PairAbstractComponentsByReference.
