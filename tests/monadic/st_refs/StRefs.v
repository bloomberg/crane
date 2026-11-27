(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** ST references: create, read, write and swap mutable cells holding
    naturals or booleans. Proofs are in [StRefsProofs]. *)

From Stdlib Require Import Arith.PeanoNat.

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
Local Open Scope monad_scope.

Section NatRefs.

  Context {R : STRefs}.
  Notation E0 := (STEvent R (fun _ : nat => nat) +' exceptE Err).

  Definition new_and_read_both_nat : itree E0 (nat * nat) :=
    r1 <- newSTRef 5;;
    r2 <- newSTRef 6;;
    x1 <- readSTRef r1;;
    x2 <- readSTRef r2;;
    Ret (x1, x2).

  Definition tree_simp_nat : itree E0 nat :=
    v <- newSTRef 5;;
    readSTRef v.

  (** A reference is of an abstract type: no location can be read out of
      it. *)
  Fail Definition location_of (v : STRef nat) : nat := v.

  Definition tree_simp_another_nat : itree E0 nat :=
    v <- newSTRef 5;;
    writeSTRef v 6;;
    readSTRef v.

  (** [swap] from "Lazy Functional State Threads" (Launchbury and Peyton
      Jones). *)
  Definition swap (v w : STRef nat) : itree E0 unit :=
    a <- readSTRef v;;
    b <- readSTRef w;;
    writeSTRef v b;;
    writeSTRef w a.

  Definition swapped : itree E0 (nat * nat) :=
    v <- newSTRef 1;;
    w <- newSTRef 2;;
    swap v w;;
    a <- readSTRef v;;
    b <- readSTRef w;;
    Ret (a, b).

End NatRefs.

Section BoolRefs.

  Context {R : STRefs}.
  Notation E0 := (STEvent R (fun _ : nat => bool) +' exceptE Err).

  Definition new_and_read_both_bool : itree E0 (bool * bool) :=
    r1 <- newSTRef false;;
    r2 <- newSTRef true;;
    x1 <- readSTRef r1;;
    x2 <- readSTRef r2;;
    Ret (x1, x2).

  Definition tree_simp_bool : itree E0 bool :=
    v <- newSTRef true;;
    readSTRef v.

End BoolRefs.

(** A program cannot return one of its references: the result type of
    [runST]'s argument does not mention [R]. *)
Fail Definition leaked := runST (fun R => newSTRef (R := R) (V := fun _ : nat => nat) 5).

Module StRefs.
  Definition new_and_read_both_nat : nat * nat := run_st (new_and_read_both_nat (R := cpp_refs)).
  Definition tree_simp_nat : nat := run_st (tree_simp_nat (R := cpp_refs)).
  Definition tree_simp_another_nat : nat := run_st (tree_simp_another_nat (R := cpp_refs)).
  Definition swapped : nat * nat := run_st (swapped (R := cpp_refs)).
  Definition new_and_read_both_bool : bool * bool := run_st (new_and_read_both_bool (R := cpp_refs)).
  Definition tree_simp_bool : bool := run_st (tree_simp_bool (R := cpp_refs)).
End StRefs.

Crane Extraction "st_refs" StRefs.
