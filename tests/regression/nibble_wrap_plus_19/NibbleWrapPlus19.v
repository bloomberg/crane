(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: nibble_of_nat wraps values modulo 16. *)

From Stdlib Require Import Nat.

Module NibbleWrapPlus19.

Definition nibble_of_nat (n : nat) : nat := n mod 16.

Definition t : nat := nibble_of_nat 19.

End NibbleWrapPlus19.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "nibble_wrap_plus_19" NibbleWrapPlus19.
