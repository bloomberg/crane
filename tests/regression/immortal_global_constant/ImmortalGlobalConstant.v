(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Set Crane SharedVariant]: a global is a constant, built once before
    [main], and every block it holds is immortal -- reached through a pair,
    a record or a list as well -- so copying or dropping any part of it
    leaves its counts alone.  A value built at run time is counted as
    before.  [long_table] is longer than the walk that marks a constant
    recurses: past a bounded depth the rest is queued, so marking it takes
    no more stack than a short one. *)

From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ImmortalGlobalConstant.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint full (d : nat) : tree :=
  match d with O => Leaf | S k => Node (full k) d (full k) end.

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 0 | Node l _ r => S (size l + size r) end.

Record entry : Type := { key : nat; value : tree }.

Definition table : tree := full 4.

Definition pair_table : tree * list tree := (full 2, [full 1; full 3]).

Definition entry_table : entry := {| key := 7; value := full 3 |}.

Fixpoint upto (n : nat) (acc : list nat) : list nat :=
  match n with O => acc | S k => upto k (n :: acc) end.

Definition long_table : list nat := upto 100000 [].

(** Built at run time: counted. *)
Definition fresh (d : nat) : tree := full d.

(** A copy of the global per call. *)
Definition sizes (n : nat) : nat :=
  fold_left (fun acc _ => acc + size table) (upto n []) 0.

End ImmortalGlobalConstant.

Set Crane SharedVariant.
(** [upto] builds the long list in a loop rather than 100000 frames deep. *)
Set Crane Loopify.
Crane Extraction "immortal_global_constant" ImmortalGlobalConstant.
