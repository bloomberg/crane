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

(* Z operations *)
Crane Extract Inlined Constant Z.add => "(%a0 + %a1)".
Crane Extract Inlined Constant Z.sub => "(%a0 - %a1)".
Crane Extract Inlined Constant Z.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant Z.div => "(%a1 == 0 ? INT64_C(0) : %a0 / %a1)".
Crane Extract Inlined Constant Z.modulo => "(%a1 == 0 ? INT64_C(0) : %a0 % %a1)".
Crane Extract Inlined Constant Z.opp => "(-%a0)".
Crane Extract Inlined Constant Z.abs => "bsl::abs(%a0)" From "bsl_cstdlib.h".
Crane Extract Inlined Constant Z.succ => "(%a0 + 1)".
Crane Extract Inlined Constant Z.pred => "(%a0 - 1)".
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
Crane Extract Inlined Constant Z.abs_N => "static_cast<unsigned int>(bsl::abs(%a0))" From "bsl_cstdlib.h".
