From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module AllArgsErasedCall.
  (** A definition whose only argument is a proof takes no C++ parameters, so
      it is emitted as a data member rather than a nullary function.  Its use
      sites must spell it [p], not [p()]. *)
  Definition p (H : 1 = 1) : nat := 7.

  Definition run (k : nat) : nat := p eq_refl + k.
End AllArgsErasedCall.

Crane Extraction "all_args_erased_call" AllArgsErasedCall.
