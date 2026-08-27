From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** WIP: A `sig` whose payload is a function, passed as a *parameter* (so its C++
    type is the concrete `Sig<std::function<uint64_t(uint64_t)>>`), is still
    applied through `any_cast<std::function<std::any(std::any)>>`, so the call
    yields `std::any` where `uint64_t` is required. *)

Module SigFunParamResultCast.
Definition apply_sig (f : {g : nat -> nat | g 0 = 0}) (n : nat) : nat := proj1_sig f n.
Definition idf : {g : nat -> nat | g 0 = 0} := exist _ (fun n => n) eq_refl.
Definition go : nat := apply_sig idf 2.
End SigFunParamResultCast.
Crane Extraction "sig_fun_param_result_cast" SigFunParamResultCast.
