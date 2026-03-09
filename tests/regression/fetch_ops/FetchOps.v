(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Fetch operations: byte fetching, pair windows, and pointer updates. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module FetchOps.

Record state : Type := mkState {
  rom : list nat
}.

(* ===== Basic byte fetching ===== *)

Definition fetch_byte (s : state) (addr : nat) : nat :=
  nth addr (rom s) 0.

(* Default to zero out of ROM range *)
Definition fetch_default_test : nat := fetch_byte (mkState [1; 2]) 5.

(* Direct fetch in range *)
Definition fetch_byte_direct (rom_data : list nat) (addr : nat) : nat :=
  nth addr rom_data 0.

Definition fetch_in_range_test : nat := fetch_byte_direct [11; 22; 33] 1.

(* ===== Drop helper for window operations ===== *)

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | 0 => l
  | S n' =>
      match l with
      | [] => []
      | _ :: l' => drop n' l'
      end
  end.

(* ===== Pair window fetching ===== *)

Definition fetch_pair (rom_data : list nat) (addr : nat) : nat * nat :=
  match drop addr rom_data with
  | b1 :: b2 :: _ => (b1, b2)
  | _ => (0, 0)
  end.

Definition fetch_pair_test : nat :=
  let p := fetch_pair [1; 2; 3] 0 in
  fst p + snd p.

(* ===== Window with next pointer ===== *)

Definition fetch_window (rom_data : list nat) (addr : nat) : option (nat * nat) :=
  match drop addr rom_data with
  | b1 :: b2 :: _ => Some (b1, addr + 2)
  | _ => None
  end.

Definition fetch_window_test : nat :=
  match fetch_window [9; 8; 7] 0 with
  | Some (_, next) => next
  | None => 0
  end.

(* ===== Combined test output ===== *)

Definition t : nat * nat * nat * nat :=
  (fetch_default_test, fetch_in_range_test, fetch_pair_test, fetch_window_test).

End FetchOps.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "fetch_ops" FetchOps.
