(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined regression tests for program loading operations. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LoadProgram.

(* Shared utility: update nth element of a list *)
Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

(* State record with PROM parameters (for tests 1-6) *)
Record state : Type := mkState {
  rom : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

(* Extended state record with additional fields (for test 4) *)
Record state_extended : Type := mkStateExtended {
  regs_len : nat;
  rom_ext : list nat;
  pc : nat;
  stack_len : nat;
  prom_addr_ext : nat;
  prom_data_ext : nat;
  prom_enable_ext : bool
}.

(* Simplified state record (for test 7) *)
Record state_simple : Type := MkState {
  rom_ : list nat;
  ptr' : nat
}.

(* PROM operations for standard state *)
Definition set_prom_params (s : state) (addr data : nat) (enable : bool) : state :=
  mkState (rom s) addr data enable.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState new_rom (prom_addr s) (prom_data s) (prom_enable s).

Fixpoint load_program (s : state) (base : nat) (bytes : list nat) : state :=
  match bytes with
  | [] => s
  | b :: rest =>
      let s' := set_prom_params s base b true in
      let s'' := execute_wpm s' in
      load_program s'' (base + 1) rest
  end.

(* PROM operations for extended state *)
Definition set_prom_params_ext (s : state_extended) (addr data : nat) (enable : bool) : state_extended :=
  mkStateExtended (regs_len s) (rom_ext s) (pc s) (stack_len s) addr data enable.

Definition execute_wpm_ext (s : state_extended) : state_extended :=
  let new_rom := if prom_enable_ext s
                 then update_nth (prom_addr_ext s) (prom_data_ext s) (rom_ext s)
                 else rom_ext s in
  mkStateExtended (regs_len s) new_rom (pc s) (stack_len s) (prom_addr_ext s) (prom_data_ext s) (prom_enable_ext s).

(* Simple sequential write operations *)
Definition write_byte (s : state_simple) (b : nat) : state_simple :=
  MkState (update_nth (ptr' s) b (rom_ s)) (S (ptr' s)).

Fixpoint load_program_simple (s : state_simple) (bytes : list nat) : state_simple :=
  match bytes with
  | [] => s
  | b :: rest => load_program_simple (write_byte s b) rest
  end.

(* Test 1: loading an empty program leaves ROM unchanged *)
Definition test_load_program_nil : bool :=
  let sample := mkState [10; 11; 12; 13] 0 0 false in
  let after := load_program sample 1 [] in
  andb (Nat.eqb (nth 0 (rom after) 0) 10)
    (andb (Nat.eqb (nth 1 (rom after) 0) 11)
      (andb (Nat.eqb (nth 2 (rom after) 0) 12)
            (Nat.eqb (nth 3 (rom after) 0) 13))).

(* Test 2: loading a non-empty program writes successive ROM bytes from the base address *)
Definition test_load_program_cons_rom : bool :=
  let sample := mkState [10; 11; 12; 13] 0 0 false in
  let after := load_program sample 1 [99; 88] in
  andb (Nat.eqb (nth 0 (rom after) 0) 10)
    (andb (Nat.eqb (nth 1 (rom after) 0) 99)
      (andb (Nat.eqb (nth 2 (rom after) 0) 88)
            (Nat.eqb (nth 3 (rom after) 0) 13))).

(* Test 3: loading a whole byte list preserves ROM length *)
Definition test_load_preserves_rom_length : bool :=
  let sample := mkState [10; 11; 12; 13] 0 0 false in
  let after := load_program sample 1 [99; 88; 77] in
  Nat.eqb (length (rom after)) 4.

(* Test 4: a single PROM programming step preserves basic state shape invariants *)
Definition test_load_program_step_preserves_wf_simple : bool :=
  let sample := mkStateExtended 4 [10; 11; 12; 13] 100 2 0 0 false in
  let after := execute_wpm_ext (set_prom_params_ext sample 1 99 true) in
  andb (Nat.eqb (regs_len after) 4)
    (andb (Nat.eqb (length (rom_ext after)) 4)
      (andb (Nat.ltb (pc after) 4096)
            (Nat.leb (stack_len after) 3))).

(* Test 5: a single PROM programming step preserves ROM length *)
Definition test_load_program_step_rom_length_weak : bool :=
  let sample := mkState [10; 11; 12; 13] 0 0 false in
  let after := execute_wpm (set_prom_params sample 1 99 true) in
  Nat.eqb (length (rom after)) 4.

(* Test 6: a single PROM programming step writes the byte at the base address *)
Definition test_load_program_step_writes_at_base : bool :=
  let sample := mkState [10; 11; 12; 13] 0 0 false in
  let after := execute_wpm (set_prom_params sample 1 99 true) in
  Nat.eqb (nth 1 (rom after) 0) 99.

(* Test 7: recursive load_program over bytes *)
Definition test_sequential_program_load : nat :=
  let sample := MkState [0; 0; 0; 0; 0] 1 in
  nth 2 (rom_ (load_program_simple sample [5; 6; 7])) 0.

(* Combined result tuple *)
Definition t : (bool * bool * bool * bool * bool * bool * nat) :=
  (test_load_program_nil,
   test_load_program_cons_rom,
   test_load_preserves_rom_length,
   test_load_program_step_preserves_wf_simple,
   test_load_program_step_rom_length_weak,
   test_load_program_step_writes_at_base,
   test_sequential_program_load).

End LoadProgram.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "load_program" LoadProgram.
