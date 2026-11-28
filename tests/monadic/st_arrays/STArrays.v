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
  Mapping.NatInt
  Monads.Error
  Monads.ITree
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section NatArrays.

  (** The programs are polymorphic in [R], as [ST.run] requires. *)
  Context {R : ST.Refs}.
  (** Effects of a program whose store holds only [nat]s. *)
  Notation E0 := (ST.Event R (fun _ : nat => nat) +' exceptE Err).

  (** Reads cell [1] of six fives. *)
  Definition array_simp_fixed_init : itree E0 nat :=
    arr <- ST.new_array 6 5;;
    ST.read_array arr 1.

  (** The first element, the length and the elements of an array from a list. *)
  Definition array_simp_list : itree E0 (nat * nat * list nat) :=
    arr <- ST.array_of_list [5; 4; 3; 2];;
    elem <- ST.read_array arr 0;;
    lst <- ST.array_to_list arr;;
    Ret (elem, length lst, lst).

  (** [xs] with its first and last elements exchanged in place. *)
  Definition swap_first_and_last_list (xs : list nat) : itree E0 (list nat) :=
    arr <- ST.array_of_list xs;;
    ST.swap_array arr 0 (length xs - 1);;
    ST.array_to_list arr.

End NatArrays.

Module STArrays.
  (** [array_simp_fixed_init] at the C++ references. *)
  Definition array_simp_fixed_init := @array_simp_fixed_init ST.cpp_refs.
  (** [array_simp_list] at the C++ references. *)
  Definition array_simp_list := @array_simp_list ST.cpp_refs.
  (** [swap_first_and_last_list] at the C++ references. *)
  Definition swap_first_and_last_list := @swap_first_and_last_list ST.cpp_refs.
  (** [List.nth] on [nat], extracted for the C++ test driver. *)
  Definition nth := Eval unfold List.nth in (@List.nth nat).
End STArrays.

Crane Extraction "st_arrays" STArrays.
