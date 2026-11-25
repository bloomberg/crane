(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** ST arrays: allocate an array (filled with a default or from a list),
    read, swap and read back its elements. Proofs are in [StArraysProofs]. *)

From Stdlib Require Import
  Arith.PeanoNat
  List
.

From ITree Require Import
  Events.Exception
  ITree
.

From Crane Require Import
  Mapping.NatIntStd
  Monads.Error
  Monads.ITree
  Monads.STMonad
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section NatArrays.

  Context {R : STRefs}.
  Notation E0 := (STEvent R (fun _ : nat => nat) +' exceptE Err).

  Definition array_simp_fixed_init : itree E0 nat :=
    arr <- newArray 6 5;;
    readArray arr 1.

  Definition array_simp_list : itree E0 (nat * nat * list nat) :=
    arr <- newListArray [5; 4; 3; 2];;
    elem <- readArray arr 0;;
    lst <- getElems arr;;
    Ret (elem, length lst, lst).

  Definition swap_first_and_last_list (xs : list nat) : itree E0 (list nat) :=
    arr <- newListArray xs;;
    swapArray arr 0 (length xs - 1);;
    getElems arr.

End NatArrays.

Module StArrays.
  Definition array_simp_fixed_init := @array_simp_fixed_init cpp_refs.
  Definition array_simp_list := @array_simp_list cpp_refs.
  Definition swap_first_and_last_list := @swap_first_and_last_list cpp_refs.
  Definition nth := Eval unfold List.nth in (@List.nth nat).
End StArrays.

Crane Extraction "st_arrays" StArrays.
