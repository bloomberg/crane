(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.NIntBDE.
From Stdlib Require Import BinInt.

(** Extraction of [Z] (binary integers) to [int64_t] (BDE flavor).

    Builds on [NIntBDE.v] which already extracts [positive] and [N].
    Maps [Z] to [int64_t] with native C++ arithmetic.
*)

Crane Extract Inductive Z =>
  "int64_t"
  [ "INT64_C(0)" "static_cast<int64_t>(%a0)" "(-static_cast<int64_t>(%a0))" ]
  "if (%scrut == 0) { %br0 } else if (%scrut > 0) { unsigned int %b1a0 = static_cast<unsigned int>(%scrut); %br1 } else { unsigned int %b2a0 = static_cast<unsigned int>(-%scrut); %br2 }"
  From "cstdint".

Crane Extract Numeral Z => "INT64_C(%n)".

(* Z operations.

   [Z] is unbounded in Rocq but represented as [int64_t] here, so operations
   that exceed the 64-bit range cannot match Rocq exactly. What we can and do
   guarantee is that they never execute C++ *undefined behavior*: signed
   overflow, negation/abs of INT64_MIN, and INT64_MIN / -1 are all UB, which an
   optimizer may miscompile in ways that silently invalidate the verified
   source's assumptions (CWE-190 / CWE-682). Each arithmetic op is therefore
   computed in the unsigned domain, where wraparound is well-defined, and cast
   back (C++20 mandates two's-complement, so the round-trip is defined). For
   inputs whose true result fits in int64_t this is identical to native signed
   arithmetic; only the out-of-range cases differ, and there they wrap
   deterministically instead of being UB. *)
Crane Extract Inlined Constant Z.add =>
  "static_cast<int64_t>(static_cast<uint64_t>(%a0) + static_cast<uint64_t>(%a1))".
Crane Extract Inlined Constant Z.sub =>
  "static_cast<int64_t>(static_cast<uint64_t>(%a0) - static_cast<uint64_t>(%a1))".
Crane Extract Inlined Constant Z.mul =>
  "static_cast<int64_t>(static_cast<uint64_t>(%a0) * static_cast<uint64_t>(%a1))".
(* Rocq's Z.div / Z.modulo use *floored* division (the remainder takes the sign
   of the divisor), whereas C++ / and % truncate toward zero. We compute the
   truncated quotient/remainder once and apply the flooring correction so the
   results match Rocq for negative operands, and follow Rocq's a/0 = 0 and
   a mod 0 = a conventions for a zero divisor (CWE-682). The [_b == -1] case is
   handled separately because INT64_MIN / -1 and INT64_MIN % -1 are UB. *)
Crane Extract Inlined Constant Z.div =>
"[&]() -> int64_t {
  int64_t _a = %a0;
  int64_t _b = %a1;
  if (_b == 0) return INT64_C(0);
  if (_b == -1) return static_cast<int64_t>(-static_cast<uint64_t>(_a));
  int64_t _q = _a / _b;
  int64_t _r = _a % _b;
  if (_r != 0 && ((_r < 0) != (_b < 0))) return _q - 1;
  return _q;
}()".
Crane Extract Inlined Constant Z.modulo =>
"[&]() -> int64_t {
  int64_t _a = %a0;
  int64_t _b = %a1;
  if (_b == 0) return _a;
  if (_b == -1) return INT64_C(0);
  int64_t _r = _a % _b;
  if (_r != 0 && ((_r < 0) != (_b < 0))) return _r + _b;
  return _r;
}()".
Crane Extract Inlined Constant Z.opp => "static_cast<int64_t>(-static_cast<uint64_t>(%a0))".
Crane Extract Inlined Constant Z.abs =>
  "(%a0 < 0 ? static_cast<int64_t>(-static_cast<uint64_t>(%a0)) : %a0)".
Crane Extract Inlined Constant Z.succ => "static_cast<int64_t>(static_cast<uint64_t>(%a0) + 1)".
Crane Extract Inlined Constant Z.pred => "static_cast<int64_t>(static_cast<uint64_t>(%a0) - 1)".
Crane Extract Inlined Constant Z.eqb => "%a0 == %a1".
Crane Extract Inlined Constant Z.ltb => "%a0 < %a1".
Crane Extract Inlined Constant Z.leb => "%a0 <= %a1".
Crane Extract Inlined Constant Z.gtb => "%a0 > %a1".
Crane Extract Inlined Constant Z.geb => "%a0 >= %a1".
Crane Extract Inlined Constant Z.min => "bsl::min(%a0, %a1)" From "bsl_algorithm.h".
Crane Extract Inlined Constant Z.max => "bsl::max(%a0, %a1)" From "bsl_algorithm.h".

(* Conversions *)
Crane Extract Inlined Constant Z.of_nat => "static_cast<int64_t>(%a0)".
Crane Extract Inlined Constant Z.to_nat => "static_cast<unsigned int>(%a0 < 0 ? 0 : %a0)".
Crane Extract Inlined Constant Z.of_N => "static_cast<int64_t>(%a0)".
Crane Extract Inlined Constant Z.to_N => "static_cast<unsigned int>(%a0 < 0 ? 0 : %a0)".
Crane Extract Inlined Constant Z.abs_N =>
  "static_cast<unsigned int>(%a0 < 0 ? -static_cast<uint64_t>(%a0) : static_cast<uint64_t>(%a0))".
