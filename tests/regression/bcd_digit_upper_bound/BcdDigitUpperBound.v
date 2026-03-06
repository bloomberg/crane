(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: BCD digit upper-bound check. *)

From Stdlib Require Import Nat Bool.

Module BcdDigitUpperBound.

Definition is_bcd_digitb (n : nat) : bool :=
  n <=? 9.

Definition t : nat :=
  (if is_bcd_digitb 7 then 1 else 0) +
  (if is_bcd_digitb 12 then 1 else 0).

End BcdDigitUpperBound.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "bcd_digit_upper_bound" BcdDigitUpperBound.
