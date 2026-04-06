From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import BinInt.
Require Import Crane.Mapping.ZInt.

Module ZDivMin.
  (** Z.div and Z.modulo mapped to int64_t division/modulo.
      Both have zero guards but miss the INT64_MIN / -1 case.
      In C++, INT64_MIN / -1 overflows (result doesn't fit in int64_t) → UB.
      In Rocq, Z.div is defined for all inputs (arbitrary precision). *)

  (** Build INT64_MIN = -9223372036854775808 via Z.opp(Z.of_nat ...) *)
  Definition neg_max : Z := Z.opp 9223372036854775807%Z.
  Definition int64_min : Z := Z.pred neg_max.

  (** INT64_MIN / -1 = 9223372036854775808, which doesn't fit in int64_t.
      In Rocq: perfectly fine, result is positive.
      In C++: signed division overflow → undefined behavior. *)
  Definition div_min_neg1 : Z := Z.div int64_min (-1)%Z.

  (** The result should be positive (dividing negative by negative). *)
  Definition div_is_positive : bool := Z.ltb 0%Z div_min_neg1.

  (** INT64_MIN % -1 = 0 in Rocq.
      In C++: also UB (same overflow issue). *)
  Definition mod_min_neg1 : Z := Z.modulo int64_min (-1)%Z.

  (** Z.opp INT64_MIN is also UB: -(INT64_MIN) overflows int64_t.
      In Rocq: result is positive 9223372036854775808. *)
  Definition opp_min : Z := Z.opp int64_min.
  Definition opp_is_positive : bool := Z.ltb 0%Z opp_min.

End ZDivMin.

Crane Extraction "z_div_min" ZDivMin.
