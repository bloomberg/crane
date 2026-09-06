(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The [Nat.iter] mapping in [Mapping/NatIntStd] expands to an inline loop
    whose accumulator is a local named [_acc].  A user binder of the same name
    is captured by the expansion, so the iterated function reads the loop
    accumulator instead of the user's value and the result is wrong. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.

Module IterCapture.
Definition run : nat :=
  let _acc := 100 in
  Nat.iter 3 (fun x => x + _acc) 0.
End IterCapture.

Crane Extraction "iter_capture" IterCapture.run.
