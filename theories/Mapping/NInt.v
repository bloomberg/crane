(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.
From Stdlib Require Import BinNat BinPos.

(** Extraction of [N] (binary natural numbers) to [unsigned int].

    Maps [positive] to [unsigned int] and [N] to [unsigned int].
    All [N] and [Pos] operations become native C++ arithmetic.
*)

(* positive: strictly positive binary integers *)
Crane Extract Inductive positive =>
  "unsigned int"
  [ "(2u * %a0 + 1u)" "(2u * %a0)" "1u" ]
  "if (%scrut == 1u) { %br2 } else if (%scrut % 2u != 0u) { unsigned int %b0a0 = (%scrut - 1u) / 2u; %br0 } else { unsigned int %b1a0 = %scrut / 2u; %br1 }".

(* N: natural numbers with zero *)
Crane Extract Inductive N =>
  "unsigned int"
  [ "0u" "%a0" ]
  "if (%scrut == 0u) { %br0 } else { unsigned int %b1a0 = %scrut; %br1 }".

Crane Extract Numeral N => "%nu".

(* Pos operations *)
Crane Extract Inlined Constant Pos.add => "(%a0 + %a1)".
Crane Extract Inlined Constant Pos.sub => "(%a0 - %a1)".
Crane Extract Inlined Constant Pos.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant Pos.succ => "(%a0 + 1u)".
Crane Extract Inlined Constant Pos.pred => "(%a0 - 1u)".
Crane Extract Inlined Constant Pos.eqb => "%a0 == %a1".
Crane Extract Inlined Constant Pos.ltb => "%a0 < %a1".
Crane Extract Inlined Constant Pos.leb => "%a0 <= %a1".
Crane Extract Inlined Constant Pos.min => "std::min(%a0, %a1)" From "algorithm".
Crane Extract Inlined Constant Pos.max => "std::max(%a0, %a1)" From "algorithm".

(* N operations *)
Crane Extract Inlined Constant N.add => "(%a0 + %a1)".
Crane Extract Inlined Constant N.sub => "(%a0 >= %a1 ? %a0 - %a1 : 0u)".
Crane Extract Inlined Constant N.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant N.div => "(%a1 == 0u ? 0u : %a0 / %a1)".
Crane Extract Inlined Constant N.modulo => "(%a1 == 0u ? 0u : %a0 % %a1)".
Crane Extract Inlined Constant N.succ => "(%a0 + 1u)".
Crane Extract Inlined Constant N.pred => "(%a0 == 0u ? 0u : %a0 - 1u)".
Crane Extract Inlined Constant N.eqb => "%a0 == %a1".
Crane Extract Inlined Constant N.ltb => "%a0 < %a1".
Crane Extract Inlined Constant N.leb => "%a0 <= %a1".
Crane Extract Inlined Constant N.min => "std::min(%a0, %a1)" From "algorithm".
Crane Extract Inlined Constant N.max => "std::max(%a0, %a1)" From "algorithm".
Crane Extract Inlined Constant N.double => "(%a0 * 2u)".
Crane Extract Inlined Constant N.succ_double => "(%a0 * 2u + 1u)".

(* Conversions *)
Crane Extract Inlined Constant N.of_nat => "static_cast<unsigned int>(%a0)".
Crane Extract Inlined Constant N.to_nat => "static_cast<unsigned int>(%a0)".
Crane Extract Inlined Constant Pos.of_nat => "static_cast<unsigned int>(%a0 == 0u ? 1u : %a0)".
Crane Extract Inlined Constant Pos.to_nat => "static_cast<unsigned int>(%a0)".
