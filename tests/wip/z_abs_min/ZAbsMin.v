From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import BinInt.
Require Import Crane.Mapping.ZInt.

Module ZAbsMin.

  (** Diagnosis (2026-11-24): not fixable under the current design. The
      undefined behaviour this test was written for is gone: every ZInt
      operation ([Z.add], [Z.sub], [Z.mul], [Z.opp], [Z.abs], [Z.succ],
      [Z.pred], [Z.div], [Z.modulo]) is computed in [uint64_t] and cast back,
      and [Z.div]/[Z.modulo] special-case a [-1] divisor, so nothing here is
      UB any more (see the comment above [std_z_add_mapping] in
      theories/Mapping/ZInt.v). What the assertions ask for is Rocq's exact
      result, and that result does not fit: [Z.abs (-2^63)] is [2^63], one
      past [INT64_MAX]. An [int64_t] cannot hold it, so no guard can return
      it. The only choices are the present deterministic two's-complement
      wrap, a trap (abort) on an out-of-range result, or a wider
      representation; the last breaks the fairness rule (no representation of
      [Z] that OCaml extraction does not also use), and wrap-versus-trap is a
      policy decision for the ZInt mapping as a whole, not a defect in one
      operation. Kept in wip until that decision is made; if it is "wrap",
      rewrite the assertions to the wrapped values and move the test. *)

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
