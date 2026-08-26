(* WIP: a sig whose payload is a function erases to std::any; the projection is used as uint64_t without an any_cast. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module SigFunPayload.
Definition mk : { f : nat -> nat | True } := exist _ (fun x => x + 1) I.
Definition go : nat := proj1_sig mk 4.
End SigFunPayload.
Crane Extraction "sig_fun_payload" SigFunPayload.
