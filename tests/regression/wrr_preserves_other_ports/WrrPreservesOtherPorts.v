(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: WRR updates only the selected ROM port. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WrrPreservesOtherPorts.

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
  mkState (acc s)
          (update_nth (sel_rom s) (acc s mod 16) (rom_ports s))
          (sel_rom s).

Definition sample : state := mkState 11 [1; 2; 3; 4] 2.
Definition t : bool := Nat.eqb (nth 0 (rom_ports (execute_wrr sample)) 0) 1.

End WrrPreservesOtherPorts.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "wrr_preserves_other_ports" WrrPreservesOtherPorts.
