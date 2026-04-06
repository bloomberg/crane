From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import BinInt.
Require Import Crane.Mapping.ZInt.

Module ZArithOverflow.
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
