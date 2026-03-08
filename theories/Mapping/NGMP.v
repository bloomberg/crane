(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.
From Stdlib Require Import BinNat BinPos.

(** Extraction of [N] (binary natural numbers) to GMP [mpz_class].

    Maps [positive] and [N] to [mpz_class] from [<gmpxx.h>].

    Requirements:
    - GMP library installed with C++ bindings (libgmpxx)
    - Link with [-lgmpxx -lgmp]
*)

(* positive: strictly positive binary integers *)
Crane Extract Inductive positive =>
  "mpz_class"
  [ "(2 * %a0 + 1)" "(2 * %a0)" "mpz_class(1)" ]
  "if (%scrut == 1) { %br2 } else if (%scrut % 2 != 0) { mpz_class %b0a0 = (%scrut - 1) / 2; %br0 } else { mpz_class %b1a0 = %scrut / 2; %br1 }"
  From "gmpxx.h".

(* N: natural numbers with zero *)
Crane Extract Inductive N =>
  "mpz_class"
  [ "mpz_class(0)" "%a0" ]
  "if (%scrut == 0) { %br0 } else { mpz_class %b1a0 = %scrut; %br1 }".

(* Pos operations *)
Crane Extract Inlined Constant Pos.add => "(%a0 + %a1)".
Crane Extract Inlined Constant Pos.sub => "(%a0 - %a1)".
Crane Extract Inlined Constant Pos.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant Pos.succ => "(%a0 + 1)".
Crane Extract Inlined Constant Pos.pred => "(%a0 - 1)".
Crane Extract Inlined Constant Pos.eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant Pos.ltb => "(%a0 < %a1)".
Crane Extract Inlined Constant Pos.leb => "(%a0 <= %a1)".
Crane Extract Inlined Constant Pos.min => "(%a0 <= %a1 ? %a0 : %a1)".
Crane Extract Inlined Constant Pos.max => "(%a0 >= %a1 ? %a0 : %a1)".

(* N operations *)
Crane Extract Inlined Constant N.add => "(%a0 + %a1)".
Crane Extract Inlined Constant N.sub => "(%a0 >= %a1 ? %a0 - %a1 : mpz_class(0))".
Crane Extract Inlined Constant N.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant N.div => "(%a1 == 0 ? mpz_class(0) : %a0 / %a1)".
Crane Extract Inlined Constant N.modulo => "(%a1 == 0 ? mpz_class(0) : %a0 % %a1)".
Crane Extract Inlined Constant N.succ => "(%a0 + 1)".
Crane Extract Inlined Constant N.pred => "(%a0 == 0 ? mpz_class(0) : %a0 - 1)".
Crane Extract Inlined Constant N.eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant N.ltb => "(%a0 < %a1)".
Crane Extract Inlined Constant N.leb => "(%a0 <= %a1)".
Crane Extract Inlined Constant N.min => "(%a0 <= %a1 ? %a0 : %a1)".
Crane Extract Inlined Constant N.max => "(%a0 >= %a1 ? %a0 : %a1)".
Crane Extract Inlined Constant N.double => "(%a0 * 2)".
Crane Extract Inlined Constant N.succ_double => "(%a0 * 2 + 1)".

(* Conversions *)
Crane Extract Inlined Constant N.of_nat => "mpz_class(%a0)".
Crane Extract Inlined Constant N.to_nat => "static_cast<unsigned int>(%a0.get_ui())".
Crane Extract Inlined Constant Pos.of_nat => "mpz_class(%a0 == 0 ? 1 : %a0)".
Crane Extract Inlined Constant Pos.to_nat => "static_cast<unsigned int>(%a0.get_ui())".
