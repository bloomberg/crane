(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: SRC then WRM then RDM restores the original accumulator through RAM. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WrmThenRdmReadsBack.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  regs : list nat;
  acc : nat;
  ram : list nat;
  sel_char : nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition execute_src (s : state) (r : nat) : state :=
  mkState (regs s) (acc s) (ram s) (get_reg_pair s r mod 16).

Definition execute_wrm (s : state) : state :=
  mkState (regs s) (acc s) (update_nth (sel_char s) (acc s) (ram s)) (sel_char s).

Definition execute_rdm (s : state) : state :=
  mkState (regs s) (nth (sel_char s) (ram s) 0) (ram s) (sel_char s).

Definition sample : state := mkState [0; 0; 1; 3; 0; 0] 12 [0; 0; 0; 5; 0] 0.
Definition roundtrip : state := execute_rdm (execute_wrm (execute_src sample 3)).
Definition t : bool := Nat.eqb (acc roundtrip) 12.

End WrmThenRdmReadsBack.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "wrm_then_rdm_reads_back" WrmThenRdmReadsBack.
