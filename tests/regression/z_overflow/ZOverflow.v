(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Bug: Z values > 2^32 produce incorrect results due to unsigned int
   overflow in the positive intermediate representation.

   Z maps to int64_t, but Z values are constructed via:
     Zpos(xI(xO(...xH...)))
   where positive maps to unsigned int (32-bit).  The xI/xO constructors
   generate (2u * %a0 + 1u) / (2u * %a0) in unsigned int arithmetic.
   For values > 2^32, the unsigned int intermediates silently overflow
   before the outer static_cast<int64_t> widens the result.

   Example: 9999999999%Z generates
     static_cast<int64_t>((2u * (2u * ...)))
   The inner chain overflows unsigned int, producing 1410065407 instead
   of 9999999999.

   Root cause: Crane Extract Numeral Z => "INT64_C(%n)" registers
   Z.of_num_int as a numeral converter, but Rocq's kernel reduces
   Z.of_num_int(digit_chain) to Zpos(binary) before extraction sees it,
   so the converter never fires.  Values always go through the binary
   positive representation with unsigned int arithmetic.

   Fix options:
   1. Add a post-reduction folder that recognizes xI/xO/xH patterns
      and folds them into integer literals.
   2. Prevent Rocq from reducing Z.of_num_int during extraction
      (e.g., declare it opaque for extraction).
   3. Use uint64_t for positive when Z mapping uses int64_t.
*)
From Corelib Require Import PrimInt63.
From Stdlib Require Import BinNat BinPos BinInt.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Import Mapping.NInt Mapping.ZInt.

Module ZOverflow.

(** 10 billion: fits in int64_t but not unsigned int *)
Definition big_z : Z := 9999999999%Z.

(** negative 10 billion *)
Definition big_neg_z : Z := (-9999999999)%Z.

(** 2^33: just over unsigned int range *)
Definition z_pow2_33 : Z := 8589934592%Z.

(** Z value that fits in unsigned int (should work) *)
Definition z_fits : Z := 1000000000%Z.

(** Nat > 2^32 also overflows unsigned int *)
Definition big_nat : nat := 4294967296.

End ZOverflow.

Crane Extraction "z_overflow" ZOverflow.
