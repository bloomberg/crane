From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module AllArgsErasedCall.
  (** A definition whose only argument is a proof is emitted as a value
      ([static inline const uint64_t p = ...]), but its use site still emits a
      call [p()]: [called object type 'uint64_t' is not a function]. *)
  Definition p (H : 1 = 1) : nat := 7.

  Definition run (k : nat) : nat := p eq_refl + k.
End AllArgsErasedCall.

Crane Extraction "all_args_erased_call" AllArgsErasedCall.
