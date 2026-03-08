(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.NGMP.
From Stdlib Require Import BinInt.

(** Extraction of [Z] (binary integers) to GMP [mpz_class].

    Builds on [NGMP.v] which already extracts [positive] and [N].
    Maps [Z] to [mpz_class] with GMP arbitrary-precision arithmetic.

    Requirements:
    - GMP library installed with C++ bindings (libgmpxx)
    - Link with [-lgmpxx -lgmp]
*)

Crane Extract Inductive Z =>
  "mpz_class"
  [ "mpz_class(0)" "%a0" "(-%a0)" ]
  "if (%scrut == 0) { %br0 } else if (%scrut > 0) { mpz_class %b1a0 = %scrut; %br1 } else { mpz_class %b2a0 = -%scrut; %br2 }".

(* Z operations *)
Crane Extract Inlined Constant Z.add => "(%a0 + %a1)".
Crane Extract Inlined Constant Z.sub => "(%a0 - %a1)".
Crane Extract Inlined Constant Z.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant Z.div => "(%a1 == 0 ? mpz_class(0) : %a0 / %a1)".
Crane Extract Inlined Constant Z.modulo => "(%a1 == 0 ? mpz_class(0) : %a0 % %a1)".
Crane Extract Inlined Constant Z.opp => "(-%a0)".
Crane Extract Inlined Constant Z.abs => "abs(%a0)".
Crane Extract Inlined Constant Z.succ => "(%a0 + 1)".
Crane Extract Inlined Constant Z.pred => "(%a0 - 1)".
Crane Extract Inlined Constant Z.eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant Z.ltb => "(%a0 < %a1)".
Crane Extract Inlined Constant Z.leb => "(%a0 <= %a1)".
Crane Extract Inlined Constant Z.gtb => "(%a0 > %a1)".
Crane Extract Inlined Constant Z.geb => "(%a0 >= %a1)".
Crane Extract Inlined Constant Z.min => "(%a0 <= %a1 ? %a0 : %a1)".
Crane Extract Inlined Constant Z.max => "(%a0 >= %a1 ? %a0 : %a1)".

(* Conversions *)
Crane Extract Inlined Constant Z.of_nat => "mpz_class(%a0)".
Crane Extract Inlined Constant Z.to_nat => "static_cast<unsigned int>(%a0 < 0 ? 0 : %a0.get_ui())".
Crane Extract Inlined Constant Z.of_N => "mpz_class(%a0)".
Crane Extract Inlined Constant Z.to_N => "(%a0 < 0 ? mpz_class(0) : %a0)".
Crane Extract Inlined Constant Z.abs_N => "abs(%a0)".
