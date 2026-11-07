(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A value of a functor's body initialised by an expression holding a lambda
    that captures: a functor's value is a function-local static (a Meyers
    singleton), where a capture is legal, and the initialiser is invoked in
    place there as it is in a struct's static member, where it is not. *)

From Stdlib Require Import List.
Import ListNotations.

Module CapturingInitialiserMeyers.

Module Type Base.
  Parameter base : nat.
End Base.

Module Sums (B : Base).
  Definition shifted_sum : nat :=
    let k := B.base + 1 in
    fold_left Nat.add (map (fun x => x + k) [1; 2; 3]) 0.
End Sums.

Module Four.
  Definition base := 4.
End Four.

Module SumsFour := Sums Four.

Definition shifted_sum_four : nat := SumsFour.shifted_sum.

End CapturingInitialiserMeyers.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "capturing_initialiser_meyers" CapturingInitialiserMeyers.
