(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** ST arrays: allocate an array (filled with a default or from a list),
    read, swap and read back its elements. Proofs are in [STArraysProofs]. *)

From Stdlib Require Import
  Arith.PeanoNat
  List
.

From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Monads.ST.
From Crane Require Import
  Mapping.NatIntStd
  Monads.Error
  Monads.ITree
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section NatArrays.

  Context {R : ST.Refs}.
  Notation E0 := (ST.Event R (fun _ : nat => nat) +' exceptE Err).

  Definition array_simp_fixed_init : itree E0 nat :=
    arr <- ST.new_array 6 5;;
    ST.read_array arr 1.

  Definition array_simp_list : itree E0 (nat * nat * list nat) :=
    arr <- ST.array_of_list [5; 4; 3; 2];;
    elem <- ST.read_array arr 0;;
    lst <- ST.array_to_list arr;;
    Ret (elem, length lst, lst).

  Definition swap_first_and_last_list (xs : list nat) : itree E0 (list nat) :=
    arr <- ST.array_of_list xs;;
    ST.swap_array arr 0 (length xs - 1);;
    ST.array_to_list arr.

End NatArrays.

Module STArrays.
  Definition array_simp_fixed_init := @array_simp_fixed_init ST.cpp_refs.
  Definition array_simp_list := @array_simp_list ST.cpp_refs.
  Definition swap_first_and_last_list := @swap_first_and_last_list ST.cpp_refs.
  Definition nth := Eval unfold List.nth in (@List.nth nat).
End STArrays.

Crane Extraction "st_arrays" STArrays.
