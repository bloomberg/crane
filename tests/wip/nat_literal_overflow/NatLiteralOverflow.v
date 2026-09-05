From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module NatLiteralOverflow.

(** A [nat] literal too large for the 64-bit integer [nat] maps onto is
    emitted verbatim, producing an out-of-range C++ literal with no
    diagnostic from Crane. *)
Definition big : nat := 18446744073709551616.

Definition bigger : nat := 100000000000000000000000.

Definition small : nat := 5.

Definition total : nat := big + small.

Definition wraps : bool := Nat.eqb big 0.

End NatLiteralOverflow.
Crane Extraction "nat_literal_overflow" NatLiteralOverflow.
