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
  Monads.Indices
  Monads.STMonad
.

Import Monads.
Local Open Scope monad_scope.

Section NatRefs.

  Context {T S : Type}.
  Context {ltu : T -> T -> Prop}.
  Context `{Ix_Correct T ltu}.
  Context {HST : STRefClass T}.

  Let V : T -> Type := fun _ => nat.
  Let E0 := (STEvent T S V) +' exceptE Err.

  Definition new_and_read_both_nat : itree E0 (nat * nat) :=
    r1 <- newSTRef zero 5;;
    r2 <- newSTRef (suc zero) 6;;
    x1 <- readSTRef r1;;
    x2 <- readSTRef r2;;
    Ret (x1, x2).

  Definition tree_simp_nat : itree E0 nat :=
    v <- newSTRef zero 5;;
    readSTRef v.

  (** A reference index must not escape into the stored value. *)
  Fail Definition tree_escape_nat : itree E0 nat :=
    v <- newSTRef 5;;
    writeSTRef v (match v with mkSTRef _ _ idx => idx end);;
    readSTRef v.

  Definition tree_simp_another_nat : itree E0 nat :=
    v <- newSTRef zero 5;;
    writeSTRef v 6;;
    readSTRef v.

  (** [swap] from "Lazy Functional State Threads" (Launchbury and Peyton
      Jones). The reference indices are not inferred yet, so they are passed
      explicitly; without them the definition fails. *)
  Definition swap' (v w : STRef S nat) : itree E0 unit :=
    a <- readSTRef (idx := STRefToIx _ _ v) v;;
    b <- readSTRef (idx := STRefToIx _ _ w) w;;
    writeSTRef v b;;
    writeSTRef w a.

  Fail Definition swap (v w : STRef S nat) : itree E0 unit :=
    a <- readSTRef v;;
    b <- readSTRef w;;
    writeSTRef v b;;
    writeSTRef w a.

End NatRefs.

Section BoolRefs.

  Context {T S : Type}.
  Context {ltu : T -> T -> Prop}.
  Context `{Ix_Correct T ltu}.
  Context {HST : STRefClass T}.

  Let V : T -> Type := fun _ => bool.
  Let E0 := (STEvent T S V) +' exceptE Err.

  Definition new_and_read_both_bool : itree E0 (bool * bool) :=
    r1 <- newSTRef zero false;;
    r2 <- newSTRef (suc zero) true;;
    x1 <- readSTRef r1;;
    x2 <- readSTRef r2;;
    Ret (x1, x2).

  Definition tree_simp_bool : itree E0 bool :=
    v <- newSTRef zero true;;
    readSTRef v.

End BoolRefs.

Module StRefs.
  (* The index instances are unfolded so that they are extracted here. *)
  Definition nat_idx : @Ix nat Nat.le := Eval unfold nat_ix in nat_ix.
  Definition nat_stref : STRefClass nat := Eval unfold nat_ix_stref in nat_ix_stref.

  Definition new_and_read_both_nat := Eval unfold new_and_read_both_nat in (@new_and_read_both_nat nat unit Nat.le).
  Definition tree_simp_nat := Eval unfold tree_simp_nat in (@tree_simp_nat nat unit Nat.le).
  Definition tree_simp_another_nat := Eval unfold tree_simp_another_nat in (@tree_simp_another_nat nat unit Nat.le).
  Definition new_and_read_both_bool := Eval unfold new_and_read_both_bool in (@new_and_read_both_bool nat unit Nat.le).
  Definition tree_simp_bool := Eval unfold tree_simp_bool in (@tree_simp_bool nat unit Nat.le).
End StRefs.

Crane Extraction "st_refs" StRefs.
