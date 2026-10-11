(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [crane::persistent_array], the representation of [PrimArray]'s
    [array], cannot be default-constructed, and two holders need to.
    - An array of arrays: an array keeps a copy of its default element, and
      the outer array's internal constructor value-initialises it, which for
      an inner [persistent_array] calls its private default constructor.
    - An inductive whose first constructor holds an array: the inductive's
      [std::variant] default-constructs its first alternative, and with it
      the array.
    Arrays of trees, of functions, of pairs, and in records work. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Corelib Require Import PrimInt63 PrimArray.
From Crane Require Import Mapping.Std.

Module PersistentArrayDefaultConstruction.

Definition grid : array (array nat) := PrimArray.make 3%uint63 (PrimArray.make 3%uint63 0).

Definition grid2 : array (array nat) :=
  PrimArray.set grid 1%uint63 (PrimArray.set (PrimArray.get grid 1%uint63) 1%uint63 5).

Definition centre : nat := PrimArray.get (PrimArray.get grid2 1%uint63) 1%uint63.

Inductive t := T : array nat -> t | E : t.

Definition get0 (x : t) : nat := match x with T a => PrimArray.get a 0%uint63 | E => 0 end.

Definition first : nat := get0 (T (PrimArray.make 2%uint63 7)) + get0 E.

End PersistentArrayDefaultConstruction.

Crane Extraction "persistent_array_default_construction" PersistentArrayDefaultConstruction.
