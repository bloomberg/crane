From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import BinInt.
Require Import Crane.Mapping.ZInt.

Module ZAbsMin.
  (** In Rocq, [Z.abs] is total: [Z.abs z] is always non-negative.
      ZInt maps [Z.abs] to [std::abs(%a0)] (from <cstdlib>).
      But [std::abs(INT64_MIN)] is undefined behavior in C++
      because [-INT64_MIN] cannot be represented as [int64_t]. *)

  Definition my_abs (x : Z) : Z := Z.abs x.

  (** Construct INT64_MIN = -2^63 via INT64_MAX + 1 negated. *)
  Definition neg_max : Z := Z.opp 9223372036854775807%Z.
  Definition int64_min : Z := Z.pred neg_max.

  (** In Rocq, this is 9223372036854775808 (positive).
      In C++, std::abs(INT64_MIN) is UB — typically returns INT64_MIN. *)
  Definition abs_of_min : Z := Z.abs int64_min.

  (** Should always be true for Z.abs, but fails in C++. *)
  Definition is_nonneg (x : Z) : bool := Z.leb 0%Z (Z.abs x).
End ZAbsMin.

Crane Extraction "z_abs_min" ZAbsMin.
