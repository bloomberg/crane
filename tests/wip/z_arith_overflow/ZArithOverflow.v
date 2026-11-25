From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import BinInt.
Require Import Crane.Mapping.ZInt.

Module ZArithOverflow.

  (** Diagnosis (2026-11-24): not fixable under the current design. The
      undefined behaviour this test was written for is gone: every ZInt
      operation ([Z.add], [Z.sub], [Z.mul], [Z.opp], [Z.abs], [Z.succ],
      [Z.pred], [Z.div], [Z.modulo]) is computed in [uint64_t] and cast back,
      and [Z.div]/[Z.modulo] special-case a [-1] divisor, so nothing here is
      UB any more (see the comment above [std_z_add_mapping] in
      theories/Mapping/ZInt.v). What the assertions ask for is Rocq's exact
      result, and that result does not fit: [3100000000 * 3100000000] is about
      [9.6 * 10^18], above [INT64_MAX] (about [9.22 * 10^18]). An [int64_t]
      cannot hold it, so no guard can return it. The only choices are the
      present deterministic two's-complement wrap, a trap (abort) on an
      out-of-range result, or a wider representation; the last breaks the
      fairness rule (no representation of [Z] that OCaml extraction does not
      also use), and wrap-versus-trap is a policy decision for the ZInt
      mapping as a whole, not a defect in one operation. Kept in wip until
      that decision is made; if it is "wrap", rewrite the assertions to the
      wrapped values and move the test. *)

  (** Z operations mapped to int64_t arithmetic can overflow.
      Signed overflow is undefined behavior in C++.

      In Rocq, Z is arbitrary precision — no overflow possible.
      In C++, int64_t wraps or traps on overflow.

      This test constructs values near INT64_MAX using int64_t-safe
      intermediate computations, then triggers signed overflow. *)

  (** Compute 3,100,000,000 via nat -> Z conversion.
      3,100,000,000 fits in unsigned int (< 2^32) and int64_t. *)
  Definition big_z : Z := Z.of_nat 3100000000.

  (** 3,100,000,000^2 = 9,610,000,000,000,000,000 > INT64_MAX.
      In Rocq: perfectly fine (Z is arbitrary precision).
      In C++: signed integer multiplication overflow — UB. *)
  Definition overflow_mul : Z := Z.mul big_z big_z.

  (** The result should be positive (product of two positives).
      In C++ the overflowed result wraps to a negative value. *)
  Definition is_positive : bool := Z.ltb 0%Z overflow_mul.

  (** Addition near INT64_MAX *)
  Definition near_max : Z := Z.of_nat 4000000000.
  Definition near_max_sq : Z := Z.mul near_max near_max.
  (** 4*10^9 * 4*10^9 = 1.6*10^19 > INT64_MAX = 9.2*10^18 *)

  (** Negation of the most negative int64_t is also UB *)
  Definition neg_big : Z := Z.opp (Z.of_nat 4000000000).
  Definition neg_sq : Z := Z.mul neg_big neg_big.
  (** (-4*10^9)^2 = 1.6*10^19 > INT64_MAX — same overflow *)
End ZArithOverflow.

Crane Extraction "z_arith_overflow" ZArithOverflow.
