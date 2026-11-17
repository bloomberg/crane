(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a reference through a module alias is printed by the alias's
    name without first resolving to what it aliases, so the target's own
    handling is lost.
    - Under [Mapping.NInt], [NN.max] with [Module NN := BinNat.N] is
      printed [N::max] instead of the inline [std::max] [N.max] is mapped
      to: "no member named 'max' in 'N'".
    - [U.f] with [Module U := T], where [f] became a method [T::f() const]
      of the eponymous inductive, is printed as a static call [U::f(x)]:
      "no member named 'f' in 'T_Mod'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import NArith.
From Crane Require Import Mapping.NInt.

Module ModuleAliasTargetHandling.

Module NN := BinNat.N.

Definition mapped : N := NN.max 3%N 4%N.

Module T.
  Inductive T := A | B : nat -> T.
  Definition f (x : T) : nat := match x with A => 0 | B n => n end.
End T.

Module U := T.

Definition methodified : nat := U.f (T.B 3) + U.f U.A.

End ModuleAliasTargetHandling.

Crane Extraction "module_alias_target_handling" ModuleAliasTargetHandling.
