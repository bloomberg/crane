From Crane Require Import Mapping.NatInt.
From Crane Require Import Mapping.ZInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    Matching a sum value taken out of a pair literal ([match fst (inl true, 0) with inl u => .. | inr v => .. end], inside an applied observer) calls [v_mut()] on a [const Sum<bool, bool>]: "function is not marked const".  [t_2] and [t_3] are the same shape at [Sum<bool, uint64_t>] and [Sum<uint64_t, uint64_t>]. *)
Module SumMatchConstVMut.
CoInductive stream : Type := SCons : nat -> stream -> stream.

Definition t_1 : nat :=
  ((fun w7 : ((sum bool bool) * nat) => (((fun w8 : (sum bool bool) => match w8 with inl u => ((fun w9 : bool => if w9 then 1 else 2) u * 2) mod 10007 | inr v => ((fun w10 : bool => if w10 then 1 else 2) v * 2 + 1) mod 10007 end) (fst w7)) * 5 + (fun w11 : nat => w11) (snd w7)) mod 10007) ((@inl bool bool true), 0%nat)).
Definition t_2 : nat :=
  ((fun w7 : ((sum bool nat) * nat) => (((fun w8 : (sum bool nat) => match w8 with inl u => ((fun w9 : bool => if w9 then 1 else 2) u * 2) mod 10007 | inr v => (v * 2 + 1) mod 10007 end) (fst w7)) * 5 + (fun w11 : nat => w11) (snd w7)) mod 10007) ((@inr bool nat 6), 3%nat)).

Definition t_3 : nat :=
  ((fun w7 : ((sum nat nat) * nat) => (((fun w8 : (sum nat nat) => match w8 with inl u => (u * 2) mod 10007 | inr v => (v * 2 + 1) mod 10007 end) (fst w7)) * 5 + (fun w11 : nat => w11) (snd w7)) mod 10007) ((@inl nat nat 4), 1%nat)).
End SumMatchConstVMut.

Crane Extraction "sum_match_const_v_mut" SumMatchConstVMut.
