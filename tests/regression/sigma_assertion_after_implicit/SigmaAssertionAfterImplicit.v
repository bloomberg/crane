(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [sig] parameter's precondition was asserted of the C++ parameter at the
    position the [sig] had among the Rocq parameters that carry values,
    counting one that [Crane Extraction Implicit] removes.  After a removed
    parameter every assertion moved one parameter on: [x]'s [n > 5] was
    asserted of [y], which its own type keeps below 3, so every call
    aborted, and the last [sig]'s precondition was dropped. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module SigmaAssertionAfterImplicit.

Definition f (k : nat) (x : {n : nat | n > 5}) (y : {n : nat | n < 3}) : nat :=
  proj1_sig x + proj1_sig y.

Definition test : nat := f 0 (exist (fun n => n > 5) 7 ltac:(repeat constructor)) (exist (fun n => n < 3) 1 ltac:(repeat constructor)).

End SigmaAssertionAfterImplicit.

Crane Extraction Implicit SigmaAssertionAfterImplicit.f [k].
Crane Extraction "sigma_assertion_after_implicit" SigmaAssertionAfterImplicit.
