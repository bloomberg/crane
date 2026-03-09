(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Combined test: modulo wrapping operations. *)

From Stdlib Require Import Nat.

Module ModuloWrap.

(* === From addr12_wrap_window === *)

Definition addr12_of_nat (n : nat) : nat := n mod 4096.

Definition test_addr12_wrap : nat := addr12_of_nat (Nat.pow 2 12 + 5).

(* === From byte_wrap === *)

Definition byte_of_nat (n : nat) : nat := n mod 256.

Definition test_byte_wrap : nat := byte_of_nat 263.

(* === From nibble_wrap === *)

Definition nibble_of_nat (n : nat) : nat := n mod 16.

Definition test_nibble_wrap : nat := nibble_of_nat 19.

(* Combined test tuple *)
Definition t : nat * nat * nat :=
  (test_addr12_wrap, test_byte_wrap, test_nibble_wrap).

End ModuloWrap.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "modulo_wrap" ModuloWrap.
