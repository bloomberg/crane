(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A [Crane Extract Numeral] literal of 2^63 or more keeps its value instead
    of wrapping in 64-bit signed arithmetic. *)
From Stdlib Require Import ZArith.
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.ZGMP.

(** [Mapping.ZGMP] writes [mpz_class(%n)], a C++ integer literal, which
    cannot hold these; gmpxx's own literal suffix reads the digits. *)
Crane Extract Numeral Z => "(%n_mpz)".

Module NumeralWrapGmp.
Local Open Scope Z_scope.

Definition two62 : Z := 4611686018427387904.
Definition two63 : Z := 9223372036854775808.
Definition two64 : Z := 18446744073709551616.
Definition two64_1 : Z := 18446744073709551617.
Definition two128 : Z := 340282366920938463463374607431768211456.
Definition neg64 : Z := -18446744073709551616.

End NumeralWrapGmp.

Crane Extraction "numeral_wrap_gmp" NumeralWrapGmp.
