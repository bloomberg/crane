(* WIP: as sig_fun_payload, but with a curried function payload. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module SigCurriedPayload.
Definition mk : { f : nat -> nat -> nat | True } := exist _ Nat.add I.
Definition go : nat := proj1_sig mk 1 2.
End SigCurriedPayload.
Crane Extraction "sig_curried_payload" SigCurriedPayload.
