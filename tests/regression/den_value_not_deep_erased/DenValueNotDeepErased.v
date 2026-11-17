(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a value of a type computed from an index, [den t], is not
    erased all the way down where it is produced, and the generic consumer
    that reads it back throws [std::bad_any_cast].  [size] reads a
    [den (TList a)] as a [List<crane::obj>], since [den a] has no static
    type; but
    - the result of a call, [mk n : den (TList TNat) := seq 0 n], is stored
      as the [List<uint64_t>] it was built as;
    - the nested literal [[[1;2];[3]] : den (TList (TList TNat))] is built
      as [List<List<crane::obj>>], erased at the leaves but not at the
      inner lists.
    A one-level literal at [den (TList TNat)] is erased correctly. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module DenValueNotDeepErased.

Inductive ty := TNat | TList : ty -> ty.

Fixpoint den (t : ty) : Type := match t with TNat => nat | TList a => list (den a) end.

Fixpoint size (t : ty) : den t -> nat :=
  match t return den t -> nat with
  | TNat => fun n => n
  | TList a => fun l => fold_left (fun acc x => acc + size a x) l 0
  end.

Definition mk (n : nat) : den (TList TNat) := seq 0 n.

Definition from_call : nat := size (TList TNat) (mk 4).

Definition nested : den (TList (TList TNat)) := [[1; 2]; [3]].

Definition from_nested : nat := size (TList (TList TNat)) nested.

End DenValueNotDeepErased.

Crane Extraction "den_value_not_deep_erased" DenValueNotDeepErased.
