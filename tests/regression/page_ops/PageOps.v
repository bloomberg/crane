(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined regression tests for page arithmetic operations. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module PageOps.

(* Shared state record *)
Record state : Type := mkState {
  pc : nat
}.

(* Shared address normalization and page operations *)
Definition addr12_of_nat (n : nat) : nat := n mod 4096.
Definition page_of (p : nat) : nat := p / 256.
Definition page_base (p : nat) : nat := page_of p * 256.
Definition page_offset (p : nat) : nat := p mod 256.

(* PC increment operations *)
Definition pc_inc1 (s : state) : nat := addr12_of_nat (pc s + 1).
Definition pc_inc2 (s : state) : nat := addr12_of_nat (pc s + 2).

(* Base address computations for incremented PC *)
Definition base_for_next1 (s : state) : nat := page_base (pc_inc1 s).
Definition base_for_next2 (s : state) : nat := page_base (pc_inc2 s).

(* Page recomposition *)
Definition recompose (p : nat) : nat := page_base p + page_offset p.

(* Maximum 12-bit address *)
Definition max_addr : nat := Nat.pow 2 12 - 1.

(* Instruction set for disassemble test *)
Inductive instruction : Type :=
| NOP : instruction
| LDM : nat -> instruction.

Definition decode (b1 : nat) (b2 : nat) : instruction :=
  if b1 =? 0 then NOP else LDM (b2 mod 16).

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | 0 => l
  | S n' =>
      match l with
      | [] => []
      | _ :: l' => drop n' l'
      end
  end.

Definition disassemble (rom : list nat) (addr : nat) : option (instruction * nat) :=
  match drop addr rom with
  | b1 :: b2 :: _ => Some (decode b1 b2, addr + 2)
  | _ => None
  end.

(* Test 1: page_base aligns addresses to 256-byte boundaries *)
Definition test_page_base_alignment : nat := page_base 777 mod 256.

(* Test 2: page-base computations for next-PC addresses *)
Definition test_page_base_next_pc : nat :=
  let s := mkState 511 in
  base_for_next1 s + base_for_next2 s.

(* Test 3: base_for_next1 crosses page boundary at PC=255 *)
Definition test_page_boundary_cross : nat := base_for_next1 (mkState 255).

(* Test 4: base_for_next1 and base_for_next2 cross page boundary at PC=255 *)
Definition test_base_for_next_page_cross_1 : nat := base_for_next1 (mkState 255).
Definition test_base_for_next_page_cross_2 : nat := base_for_next2 (mkState 255).

(* Test 5: page decomposition recombines to the original address *)
Definition test_page_decomp_roundtrip : bool := Nat.eqb ((1027 / 256) * 256 + 1027 mod 256) 1027.

(* Test 6: recombine page base and page offset *)
Definition test_page_offset_recompose : nat := recompose (addr12_of_nat 1027).

(* Test 7: recombine page base and page offset (duplicate of test 6) *)
Definition test_page_recompose : nat := recompose (addr12_of_nat 1027).

(* Test 8: pc_inc2 normalizes through addr12 modulo window *)
Definition test_pc_inc2_wraparound : nat := pc_inc2 (mkState max_addr).

(* Test 9: PC increment behaviors *)
Definition test_pc_inc1_wrap : nat := pc_inc1 (mkState max_addr).
Definition test_pc_inc2_wrap : nat := pc_inc2 (mkState max_addr).
Definition test_disassemble_edge : nat :=
  match disassemble [0; 7; 9; 11] 0 with
  | Some (_, next) => next
  | None => 0
  end.

(* Combined result tuple *)
Definition t : (nat * nat * nat * nat * nat * bool * nat * nat * nat * nat * nat * nat) :=
  (test_page_base_alignment,
   test_page_base_next_pc,
   test_page_boundary_cross,
   test_base_for_next_page_cross_1,
   test_base_for_next_page_cross_2,
   test_page_decomp_roundtrip,
   test_page_offset_recompose,
   test_page_recompose,
   test_pc_inc2_wraparound,
   test_pc_inc1_wrap,
   test_pc_inc2_wrap,
   test_disassemble_edge).

End PageOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "page_ops" PageOps.
