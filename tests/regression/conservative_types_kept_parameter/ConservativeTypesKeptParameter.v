(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: under [Set Crane Extraction Conservative Types], a polymorphic
    function keeps its type binder as a parameter -- [len(crane::obj, const
    List<T1>&)] -- but neither its recursive call nor its callers pass it:
    "no matching function for call to 'len'".  The standard library's own
    [List::length] fails the same way, as "no member named 'length' in
    'crane::obj'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ConservativeTypesKeptParameter.

Fixpoint len {A} (l : list A) : nat := match l with [] => 0 | _ :: t => S (len t) end.

Definition mine : nat := len [true; false].

Definition stdlib : nat := List.length [1; 2; 3].

End ConservativeTypesKeptParameter.

Set Crane Extraction Conservative Types.
Crane Extraction "conservative_types_kept_parameter" ConservativeTypesKeptParameter.
