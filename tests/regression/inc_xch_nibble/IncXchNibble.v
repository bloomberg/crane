(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined behavioral tests for INC and XCH operations on register nibbles. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module IncXchNibble.

(* Shared helper functions *)
Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  regs : list nat;
  acc : nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition nibble_of_nat (n : nat) : nat := n mod 16.
Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

(* INC instruction: increment register, wrap to nibble *)
Definition execute_inc (s : state) (r : nat) : state :=
  mkState (update_nth r (nibble_of_nat (get_reg s r + 1)) (regs s)) (acc s).

(* XCH instruction: exchange accumulator with register, both wrapped to nibble *)
Definition execute_xch (s : state) (r : nat) : state :=
  mkState (update_nth r (nibble_of_nat (acc s)) (regs s)) (get_reg s r).

(* Test sample state *)
Definition sample : state := mkState [2; 9; 4; 7; 8; 1] 13.

(* Test 1: INC on even register (r=2) modifies only high nibble of its pair *)
Definition inc_modifies_single_nibble_even : bool :=
  Nat.eqb
    (get_reg_pair (execute_inc sample 2) 2)
    (nibble_of_nat (get_reg sample 2 + 1) * 16 + get_reg sample 3).

(* Test 2: INC on odd register (r=3) modifies only low nibble of its pair *)
Definition inc_modifies_single_nibble_odd : bool :=
  Nat.eqb
    (get_reg_pair (execute_inc sample 3) 3)
    (get_reg sample 2 * 16 + nibble_of_nat (get_reg sample 3 + 1)).

(* Test 3: INC on even register (r=2) leaves its pair partner (r=3) unchanged *)
Definition inc_preserves_pair_partner : bool :=
  Nat.eqb (get_reg (execute_inc sample 2) 3) (get_reg sample 3).

(* Test 4: INC on odd register (r=3) leaves its pair partner (r=2) unchanged *)
Definition inc_preserves_pair_partner_odd : bool :=
  Nat.eqb (get_reg (execute_inc sample 3) 2) (get_reg sample 2).

(* Test 5: XCH on even register (r=2) modifies only high nibble of its pair *)
Definition xch_modifies_single_nibble_even : bool :=
  Nat.eqb
    (get_reg_pair (execute_xch sample 2) 2)
    (nibble_of_nat (acc sample) * 16 + get_reg sample 3).

(* Test 6: XCH on odd register (r=3) modifies only low nibble of its pair *)
Definition xch_modifies_single_nibble_odd : bool :=
  Nat.eqb
    (get_reg_pair (execute_xch sample 3) 3)
    (get_reg sample 2 * 16 + nibble_of_nat (acc sample)).

(* Test 7: XCH on even register (r=2) leaves its pair partner (r=3) unchanged *)
Definition xch_preserves_pair_partner : bool :=
  Nat.eqb (get_reg (execute_xch sample 2) 3) (get_reg sample 3).

(* Test 8: XCH on odd register (r=3) leaves its pair partner (r=2) unchanged *)
Definition xch_preserves_pair_partner_odd : bool :=
  Nat.eqb (get_reg (execute_xch sample 3) 2) (get_reg sample 2).

(* Combined test: all 8 checks must pass *)
Definition t : bool :=
  inc_modifies_single_nibble_even &&
  inc_modifies_single_nibble_odd &&
  inc_preserves_pair_partner &&
  inc_preserves_pair_partner_odd &&
  xch_modifies_single_nibble_even &&
  xch_modifies_single_nibble_odd &&
  xch_preserves_pair_partner &&
  xch_preserves_pair_partner_odd.

End IncXchNibble.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "inc_xch_nibble" IncXchNibble.
