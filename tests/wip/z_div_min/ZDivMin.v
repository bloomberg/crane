From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import BinInt.
Require Import Crane.Mapping.ZInt.

Module ZDivMin.

  (** Diagnosis (2026-11-24): not fixable under the current design. The
      undefined behaviour this test was written for is gone: every ZInt
      operation ([Z.add], [Z.sub], [Z.mul], [Z.opp], [Z.abs], [Z.succ],
      [Z.pred], [Z.div], [Z.modulo]) is computed in [uint64_t] and cast back,
      and [Z.div]/[Z.modulo] special-case a [-1] divisor, so nothing here is
      UB any more (see the comment above [std_z_add_mapping] in
      theories/Mapping/ZInt.v). What the assertions ask for is Rocq's exact
      result, and that result does not fit: [Z.div (-2^63) (-1)] and [Z.opp
      (-2^63)] are both [2^63], one past [INT64_MAX] ([Z.modulo (-2^63) (-1)]
      = 0 already holds). An [int64_t] cannot hold it, so no guard can return
      it. The only choices are the present deterministic two's-complement
      wrap, a trap (abort) on an out-of-range result, or a wider
      representation; the last breaks the fairness rule (no representation of
      [Z] that OCaml extraction does not also use), and wrap-versus-trap is a
      policy decision for the ZInt mapping as a whole, not a defect in one
      operation. Kept in wip until that decision is made; if it is "wrap",
      rewrite the assertions to the wrapped values and move the test. *)

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
