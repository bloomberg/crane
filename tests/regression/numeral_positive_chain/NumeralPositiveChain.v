(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [positive] registered as a numeral: its literals are binary chains,
    not Peano ones, though [xO] is its last unary constructor and [xH] its
    last nullary one. *)

From Stdlib Require Import BinNums.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.

Crane Extract Inductive positive =>
  "uint64_t"
  [ "(2 * %a0 + 1)" "(2 * %a0)" "UINT64_C(1)" ]
  "if (%scrut == 1) { %br2 } else if (%scrut % 2) { uint64_t %b0a0 = %scrut / 2; %br0 } else { uint64_t %b1a0 = %scrut / 2; %br1 }"
  From "cstdint".

Crane Extract Numeral positive => "UINT64_C(%n)".

Module NumeralPositiveChain.

Definition two : positive := xO xH.
Definition four : positive := xO (xO xH).
Definition five : positive := xI (xO xH).
Definition six : positive := xO (xI xH).

End NumeralPositiveChain.

Crane Extraction "numeral_positive_chain" NumeralPositiveChain.
