(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: two modules of the same name, declared in different library
    files, are emitted under the one name when one of them is an alias.
    [OrderedTypeEx.Positive_as_OT] is a module of its own and
    [OrdersEx.Positive_as_OT] an alias of [BinPos.Pos].  Using both, the
    clash is noticed only halfway: some references are renamed to
    [Coq_Positive_as_OT], which is never declared, while the alias is still
    emitted under the struct's name -- "typedef redefinition with different
    types ('Coq_Pos' vs 'Positive_as_OT')", "unknown type name
    'Coq_Positive_as_OT'".  With [Nat_as_OT] the same pair is "definition of
    type 'Nat_as_OT' conflicts with type alias of the same name". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import PArith FMapList OrderedTypeEx.
From Stdlib Require OrdersEx.

Module SameNamedFileModules.

Module PM := FMapList.Make(OrderedTypeEx.Positive_as_OT).
Module P2 := OrdersEx.Positive_as_OT.

Definition m := PM.add 1%positive 2 (PM.empty nat).

Definition found : nat := match PM.find 1%positive m with Some v => v | None => 0 end.
Definition larger : bool := Pos.eqb (P2.max 3 4) 4.

End SameNamedFileModules.

Crane Extraction "same_named_file_modules" SameNamedFileModules.
