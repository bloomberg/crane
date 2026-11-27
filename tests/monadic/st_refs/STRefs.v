(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** ST references: create, read, write and swap mutable cells holding
    naturals or booleans. Proofs are in [STRefsProofs]. *)

From Stdlib Require Import Arith.PeanoNat.

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
Local Open Scope monad_scope.

Section NatRefs.

  Context {R : ST.Refs}.
  Notation E0 := (ST.Event R (fun _ : nat => nat) +' exceptE Err).

  Definition new_and_read_both_nat : itree E0 (nat * nat) :=
    r1 <- ST.new_ref 5;;
    r2 <- ST.new_ref 6;;
    x1 <- ST.read_ref r1;;
    x2 <- ST.read_ref r2;;
    Ret (x1, x2).

  Definition tree_simp_nat : itree E0 nat :=
    v <- ST.new_ref 5;;
    ST.read_ref v.

  (** A reference is of an abstract type: no location can be read out of
      it. *)
  Fail Definition location_of (v : ST.ref nat) : nat := v.

  Definition tree_simp_another_nat : itree E0 nat :=
    v <- ST.new_ref 5;;
    ST.write_ref v 6;;
    ST.read_ref v.

  (** [swap] from "Lazy Functional State Threads" (Launchbury and Peyton
      Jones). *)
  Definition swap (v w : ST.ref nat) : itree E0 unit :=
    a <- ST.read_ref v;;
    b <- ST.read_ref w;;
    ST.write_ref v b;;
    ST.write_ref w a.

  Definition swapped : itree E0 (nat * nat) :=
    v <- ST.new_ref 1;;
    w <- ST.new_ref 2;;
    swap v w;;
    a <- ST.read_ref v;;
    b <- ST.read_ref w;;
    Ret (a, b).

End NatRefs.

Section BoolRefs.

  Context {R : ST.Refs}.
  Notation E0 := (ST.Event R (fun _ : nat => bool) +' exceptE Err).

  Definition new_and_read_both_bool : itree E0 (bool * bool) :=
    r1 <- ST.new_ref false;;
    r2 <- ST.new_ref true;;
    x1 <- ST.read_ref r1;;
    x2 <- ST.read_ref r2;;
    Ret (x1, x2).

  Definition tree_simp_bool : itree E0 bool :=
    v <- ST.new_ref true;;
    ST.read_ref v.

End BoolRefs.

(** A program cannot return one of its references: the result type of
    [ST.run]'s argument does not mention [R]. *)
Fail Definition leaked := ST.run (fun R => ST.new_ref (R := R) (V := fun _ : nat => nat) 5).

Module STRefs.
  Definition new_and_read_both_nat : nat * nat := ST.run_cpp (new_and_read_both_nat (R := ST.cpp_refs)).
  Definition tree_simp_nat : nat := ST.run_cpp (tree_simp_nat (R := ST.cpp_refs)).
  Definition tree_simp_another_nat : nat := ST.run_cpp (tree_simp_another_nat (R := ST.cpp_refs)).
  Definition swapped : nat * nat := ST.run_cpp (swapped (R := ST.cpp_refs)).
  Definition new_and_read_both_bool : bool * bool := ST.run_cpp (new_and_read_both_bool (R := ST.cpp_refs)).
  Definition tree_simp_bool : bool := ST.run_cpp (tree_simp_bool (R := ST.cpp_refs)).
End STRefs.

Crane Extraction "st_refs" STRefs.
