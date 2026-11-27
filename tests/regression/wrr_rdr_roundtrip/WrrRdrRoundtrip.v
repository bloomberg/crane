(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: WRR followed by RDR returns the original accumulator value. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WrrRdrRoundtrip.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  acc : nat;
  rom_ports : list nat;
  sel_rom : nat
}.

Definition execute_wrr (s : state) : state :=
  mkState (acc s) (update_nth (sel_rom s) (acc s) (rom_ports s)) (sel_rom s).

Definition execute_rdr (s : state) : state :=
  mkState (nth (sel_rom s) (rom_ports s) 0) (rom_ports s) (sel_rom s).

Definition sample : state := mkState 13 [1; 2; 7; 4] 2.
Definition t : bool := Nat.eqb (acc (execute_rdr (execute_wrr sample))) 13.

End WrrRdrRoundtrip.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
Crane Extraction "wrr_rdr_roundtrip" WrrRdrRoundtrip.
