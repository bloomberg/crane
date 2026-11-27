(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Module Ack.

(* Ackermann function *)
Fixpoint ack (m : nat) (n : nat) : nat :=
  (fix ack_m (n : nat) : nat :=
    match m with
      | 0 => S n
      | S pm =>
        match n with
          | 0 => ack pm Nat.one
          | S pn => ack pm (ack_m pn)
        end
    end) n.
End Ack.

Require Crane.Extraction.
Require Import Crane.Mapping.Std.
Require Import Crane.Mapping.NatInt.
Crane Extraction "ack" Ack.

(* Require Extraction. *)
(* Extraction "ack.ml" Ack. *)
