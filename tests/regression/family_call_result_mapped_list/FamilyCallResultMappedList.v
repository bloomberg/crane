(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: under [Mapping.DequeList], a call's result entering a slot whose
    type is computed from an index ([den t]) is not converted to the erased
    shape at all.  [mk n : den (TList TNat) := seq 0 n] is returned as the
    [std::deque<uint64_t>] it was built as, and the generic consumer, which
    reads a [std::deque<crane::obj>], throws [std::bad_any_cast]: the
    conversion ([box_list_for_family]) skips mapped containers, and nothing
    else converts them.  A literal of the same type works. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.DequeList.

Module FamilyCallResultMappedList.

Inductive ty := TNat | TList : ty -> ty.

Fixpoint den (t : ty) : Type := match t with TNat => nat | TList a => list (den a) end.

Fixpoint size (t : ty) : den t -> nat :=
  match t return den t -> nat with
  | TNat => fun n => n
  | TList a => fun l => fold_left (fun acc x => acc + size a x) l 0
  end.

Definition mk (n : nat) : den (TList TNat) := seq 0 n.

Definition result : nat := size (TList TNat) (mk 4).

End FamilyCallResultMappedList.

Crane Extraction "family_call_result_mapped_list" FamilyCallResultMappedList.
