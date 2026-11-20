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
  Monads.Indices
  Monads.STMonad
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section NatArrays.

  Context {T S : Type}.
  Context {ltu : T -> T -> Prop}.
  Context `{Ix_Correct T ltu}.
  Context {HST : STRefClass T}.

  Let V : T -> Type := fun _ => nat.
  Let E0 := (STEvent T S V) +' exceptE Err.

  Definition array_simp_fixed_init : itree E0 nat :=
    arr <- newArray zero zero (suc (suc (suc (suc (suc zero))))) 5;;
    readArray (idx := zero) arr (suc zero).

  Definition array_simp_list : itree E0 (nat * nat * list nat) :=
    arr <- newListArray zero zero (suc (suc (suc zero))) [5; 4; 3; 2];;
    elem <- readArray (idx := zero) arr zero;;
    lst <- getElems (idx := zero) arr;;
    Ret (elem, length lst, lst).

  Definition swap_first_and_last_list (xs : list nat) : itree E0 (list nat) :=
    let lastIndex := fromNat (length xs - 1) in
    arr <- newListArray zero zero lastIndex xs;;
    swapArray (idx := zero) arr zero lastIndex;;
    getElems (idx := zero) arr.

End NatArrays.

Module StArrays.
  (* The index instances are unfolded so that they are extracted here. *)
  Definition nat_idx : @Ix nat Nat.le := Eval unfold nat_ix in nat_ix.
  Definition nat_stref : STRefClass nat := Eval unfold nat_ix_stref in nat_ix_stref.

  Definition array_simp_fixed_init := Eval unfold array_simp_fixed_init in (@array_simp_fixed_init nat unit Nat.le nat_idx nat_stref).
  Definition array_simp_list := Eval unfold array_simp_list in (@array_simp_list nat unit Nat.le nat_idx nat_stref).
  (** [swapArray] is called, not unfolded: it takes the array as a
      [const std::shared_ptr<std::vector<uint64_t>>&]. *)
  Definition swap_first_and_last_list :=
    Eval unfold swap_first_and_last_list in
      (@swap_first_and_last_list nat unit Nat.le nat_idx nat_stref).

  Definition nth := Eval unfold List.nth in (@List.nth nat).
End StArrays.

Crane Extraction "st_arrays" StArrays.
