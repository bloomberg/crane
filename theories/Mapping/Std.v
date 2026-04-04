(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Standard-library extraction mappings.

    Maps [option], [prod], [string], [int63], and [float] to their
    C++ standard library equivalents ([std::optional], [std::pair],
    [std::string], [int64_t], [double]).

    Sets the stdlib flavor to ["std"] and the clang-format style. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Shared.

#[export] Set Crane StdLib "std".
#[export] Set Crane Format Style "{BasedOnStyle: LLVM, SeparateDefinitionBlocks: Always}".

Crane Extract Inductive option =>
  "std::optional<%t0>"
  [ "std::make_optional<%t0>(%a0)"
    "std::optional<%t0>()" ]
  "if (%scrut.has_value()) { %t0 %b0a0 = *%scrut; %br0 } else { %br1 }"
  From "optional" "memory".

Crane Extract Inductive prod =>
  "std::pair<%t0, %t1>"
  [ "std::make_pair(%a0, %a1)" ]
  "%t0 %b0a0 = %scrut.first; %t1 %b0a1 = %scrut.second; %br0"
  From "utility".
Crane Extract Inlined Constant fst => "%a0.first" From "utility".
Crane Extract Inlined Constant snd => "%a0.second" From "utility".

From Corelib Require Import PrimString.
Crane Extract Inlined Constant PrimString.char63 => "char".
Crane Extract Inlined Constant PrimString.string => "std::string" From "string".
Crane Extract Inlined Constant PrimString.cat => "%a0 + %a1" From "string".
Crane Extract Inlined Constant PrimString.get => "%a0[%a1]" From "string".
Crane Extract Inlined Constant PrimString.sub => "%a0.substr(%a1, %a2)" From "string".
Crane Extract Inlined Constant PrimString.length => "%a0.length()" From "string".

(* int63 primitives - int64_t with 63-bit masking.
   All arithmetic results are masked to [0, 2^63) to match Rocq semantics.
   Bitwise ops preserve the invariant (inputs have bit 63 = 0).
   Shifts guard against UB when shift amount >= 63. *)
From Corelib Require Import PrimInt63.
Crane Extract Inlined Constant PrimInt63.int => "int64_t" From "cstdint".
Crane Extract Inlined Constant PrimInt63.add => "((%a0 + %a1) & 0x7FFFFFFFFFFFFFFFLL)".
Crane Extract Inlined Constant PrimInt63.sub => "((%a0 - %a1) & 0x7FFFFFFFFFFFFFFFLL)".
Crane Extract Inlined Constant PrimInt63.mul => "((%a0 * %a1) & 0x7FFFFFFFFFFFFFFFLL)".
Crane Extract Inlined Constant PrimInt63.div => "(%a1 == 0 ? 0 : %a0 / %a1)".
Crane Extract Inlined Constant PrimInt63.mod => "(%a1 == 0 ? 0 : %a0 % %a1)".
Crane Extract Inlined Constant PrimInt63.eqb => "%a0 == %a1".
Crane Extract Inlined Constant PrimInt63.ltb => "%a0 < %a1".
Crane Extract Inlined Constant PrimInt63.leb => "%a0 <= %a1".
Crane Extract Inlined Constant PrimInt63.land => "(%a0 & %a1)".
Crane Extract Inlined Constant PrimInt63.lor => "(%a0 | %a1)".
Crane Extract Inlined Constant PrimInt63.lxor => "(%a0 ^ %a1)".
Crane Extract Inlined Constant PrimInt63.lsl => "(%a1 >= 63 ? 0 : ((%a0 << %a1) & 0x7FFFFFFFFFFFFFFFLL))".
Crane Extract Inlined Constant PrimInt63.lsr => "(%a1 >= 63 ? 0 : (%a0 >> %a1))".

(* PrimFloat - IEEE 754 binary64 (C++ double).
   Import PrimFloat AFTER PrimInt63 so the qualified names below resolve
   unambiguously even though both modules export [add], [sub], etc. *)
From Corelib Require Import PrimFloat.
Crane Extract Inlined Constant PrimFloat.float => "double".
Crane Extract Inlined Constant PrimFloat.add => "(%a0 + %a1)".
Crane Extract Inlined Constant PrimFloat.sub => "(%a0 - %a1)".
Crane Extract Inlined Constant PrimFloat.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant PrimFloat.div => "(%a0 / %a1)".
Crane Extract Inlined Constant PrimFloat.opp => "(-%a0)".
Crane Extract Inlined Constant PrimFloat.abs => "std::abs(%a0)" From "cmath".
Crane Extract Inlined Constant PrimFloat.sqrt => "std::sqrt(%a0)" From "cmath".
Crane Extract Inlined Constant PrimFloat.eqb => "%a0 == %a1".
Crane Extract Inlined Constant PrimFloat.ltb => "%a0 < %a1".
Crane Extract Inlined Constant PrimFloat.leb => "%a0 <= %a1".
Crane Extract Inlined Constant PrimFloat.of_uint63 => "static_cast<double>(%a0)".
