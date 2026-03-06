(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: set_test_pin updates pin and preserves accumulator. *)

From Stdlib Require Import Nat Bool.

Module SetTestPinUpdate.

Record state : Type := mkState {
  acc : nat;
  test_pin : bool
}.

Definition set_test_pin (s : state) (v : bool) : state :=
  mkState (acc s) v.

Definition t : nat :=
  let s' := set_test_pin (mkState 6 false) true in
  acc s' + (if test_pin s' then 1 else 0).

End SetTestPinUpdate.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_test_pin_update" SetTestPinUpdate.
