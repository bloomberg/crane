(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: extracting the whole standard [Nat] module -- through an alias
    [Module X := PeanoNat.Nat], or as [OrdersEx.Nat_as_OT] behind an
    [MSetAVL] instance -- erases the return types of its [EvenT]/[OddT]
    functions.  [even_EvenT], [EvenT_2] and [OddT_S_EvenT] are declared to
    return [crane::obj] while their parameters, and the aliases [using EvenT
    = Sig<uint64_t>], stay concrete: "no viable conversion from 'crane::obj'
    to 'const Sig<uint64_t>'".  [Nat.even_EvenT] extracted on its own
    returns [EvenT]; something else in the module, likely the family
    eliminators, makes [EvenT : nat -> Type] count as a value-indexed
    family. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module NatModuleFamilyReturns.

Module X := PeanoNat.Nat.

Definition result : nat := X.max 3 4.

End NatModuleFamilyReturns.

Crane Extraction "nat_module_family_returns" NatModuleFamilyReturns.
