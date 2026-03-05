(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: load_program writes bytes beginning at base address. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LoadProgramHeadWrite.

Record state : Type := mkState {
  rom : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Fixpoint update_nth (n : nat) (x : nat) (l : list nat) : list nat :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, _ => l
  end.

Definition set_prom_params (s : state) (addr : nat) (data : nat) (enable : bool) : state :=
  mkState (rom s) addr data enable.

Definition execute_wpm (s : state) : state :=
  let new_rom :=
    if prom_enable s then update_nth (prom_addr s) (prom_data s) (rom s) else rom s in
  mkState new_rom (prom_addr s) (prom_data s) (prom_enable s).

Fixpoint load_program (s : state) (base : nat) (bytes : list nat) : state :=
  match bytes with
  | [] => s
  | b :: rest =>
      let s1 := set_prom_params s base b true in
      let s2 := execute_wpm s1 in
      load_program s2 ((base + 1) mod 4096) rest
  end.

Definition t : nat :=
  let s0 := mkState [0; 0; 0; 0] 0 0 false in
  let s1 := load_program s0 1 [7; 8] in
  nth 1 (rom s1) 0.

End LoadProgramHeadWrite.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "load_program_head_write" LoadProgramHeadWrite.
