(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a call's result entering a slot whose type is computed from an
    index ([den t]) is converted to the erased shape only one level deep,
    and the generic consumer throws [std::bad_any_cast].  [mk n : den (TList
    (TPair TNat TNat))] builds a [List<std::pair<uint64_t, uint64_t>>]; the
    conversion ([box_list_for_family]) boxes each element whole, as a
    [std::pair<uint64_t, uint64_t>], where the consumer reads a
    [std::pair<crane::obj, crane::obj>].  A literal of the same type is
    built at the erased shape and works. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module FamilyCallResultDeepShape.

Inductive ty := TNat | TPair : ty -> ty -> ty | TList : ty -> ty.

Fixpoint den (t : ty) : Type :=
  match t with TNat => nat | TPair a b => (den a * den b)%type | TList a => list (den a) end.

Fixpoint sz (t : ty) : den t -> nat :=
  match t return den t -> nat with
  | TNat => fun n => n
  | TPair a b => fun p => sz a (fst p) + sz b (snd p)
  | TList a => fun l => fold_left (fun acc x => acc + sz a x) l 0
  end.

Definition mk (n : nat) : den (TList (TPair TNat TNat)) := List.map (fun k => (k, k)) (seq 0 n).

Definition result : nat := sz (TList (TPair TNat TNat)) (mk 3).

End FamilyCallResultDeepShape.

Crane Extraction "family_call_result_deep_shape" FamilyCallResultDeepShape.
