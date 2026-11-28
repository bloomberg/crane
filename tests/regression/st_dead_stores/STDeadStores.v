(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** References that are only ever written.  Scalar replacement keeps a
    reference used only where it is created in a local, and a store into it
    nothing reads is dropped with it; what is left must not be a variable
    only ever set, which [-Wunused-but-set-variable] rejects:
    - [written_only]: a reference a loop helper writes and nothing reads;
    - [read_by_dead_store]: a loop parameter read only to initialise a
      reference nothing reads -- the parameter is then only ever assigned;
    - [written_in_branch]: a reference written in one branch of a
      conditional, read in neither;
    - [written_in_unused_branch]: the same where nothing reads the
      conditional's value either: what computes it still runs, without
      the store. *)

From Stdlib Require Import Arith.PeanoNat List.
From ITree Require Import Events.Exception ITree.
From Crane Require Monads.ST.
From Crane Require Import Mapping.NatInt Monads.Error Monads.ITree.
Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Section S.
  (** The programs are polymorphic in [R], as [ST.run] requires. *)
  Context {R : ST.Refs}.
  (** Effects of a program whose store holds only [nat]s. *)
  Notation E0 := (ST.Event R (fun _ : nat => nat) +' exceptE Err).

  (** A loop helper writes [r] three times; nothing reads it. *)
  Definition written_only : itree E0 nat :=
    r <- ST.new_ref 1;;
    let fix go (k : nat) (p : ST.ref nat) : itree E0 nat :=
      match k with
      | O => Ret 7
      | Datatypes.S k' => ST.write_ref p (k' * 2);; go k' p
      end in
    go 3 r.

  (** The loop parameter [acc] only initialises a reference nothing reads. *)
  Definition read_by_dead_store : itree E0 nat :=
    let fix go (k acc : nat) : itree E0 nat :=
      match k with
      | O => Ret k
      | Datatypes.S k' => r <- ST.new_ref acc;; go k' (acc + 1)
      end in
    go 4 0.

  (** [r] is written in one branch and read in neither. *)
  Definition written_in_branch (b : bool) : itree E0 nat :=
    r <- ST.new_ref 0;;
    x <- (if b then ST.write_ref r 5;; Ret 1 else Ret 2);;
    Ret (x + 10).

  (** As [written_in_branch], with the branch's value unused but its update of [s] kept. *)
  Definition written_in_unused_branch (b : bool) : itree E0 nat :=
    r <- ST.new_ref 0;;
    s <- ST.new_ref 3;;
    x <- (if b then ST.write_ref r 5;; v <- ST.read_ref s;; ST.write_ref s (v + 1);; Ret 1 else Ret 2);;
    ST.read_ref s.
End S.

Module STDeadStores.
  (** [written_only], run in C++. *)
  Definition written_only : nat := ST.run_cpp (@written_only ST.cpp_refs).
  (** [read_by_dead_store], run in C++. *)
  Definition read_by_dead_store : nat := ST.run_cpp (@read_by_dead_store ST.cpp_refs).
  (** [written_in_branch], run in C++. *)
  Definition written_in_branch (b : bool) : nat := ST.run_cpp (@written_in_branch ST.cpp_refs b).
  (** [written_in_unused_branch], run in C++. *)
  Definition written_in_unused_branch (b : bool) : nat := ST.run_cpp (@written_in_unused_branch ST.cpp_refs b).
End STDeadStores.

Set Crane Loopify.
Crane Extraction "st_dead_stores" STDeadStores.
