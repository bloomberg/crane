(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Bloomberg Development Environment (BDE) extraction mappings.

    Maps [option], [prod], [string], [int63], and [float] to their
    BDE equivalents ([bsl::optional], [bsl::pair], [bsl::string],
    [int64_t], [double]).

    Sets the stdlib flavor to ["BDE"]. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Shared.

#[export] Set Crane StdLib "BDE".
(* If you have bde-format, you can uncomment the line below: *)
(* #[export] Set Crane Format Style "{BasedOnStyle: BDE, SeparateDefinitionBlocks: Always}". *)
#[export] Set Crane Format Style "{BasedOnStyle: LLVM, SeparateDefinitionBlocks: Always}".

Crane Extract Inductive option =>
  "bsl::optional<%t0>"
  [ "bsl::make_optional<%t0>(%a0)"
    "bsl::optional<%t0>()" ]
  "if (%scrut.has_value()) { %t0 %b0a0 = *%scrut; %br0 } else { %br1 }"
  From "bsl_optional.h" "bsl_memory.h".

Crane Extract Inductive prod =>
  "bsl::pair<%t0, %t1>"
  [ "bsl::make_pair(%a0, %a1)" ]
  "auto [%b0a0, %b0a1] = %scrut; %br0"
  From "bsl_utility.h".
Crane Extract Inlined Constant fst => "%a0.first" From "bsl_utility.h".
Crane Extract Inlined Constant snd => "%a0.second" From "bsl_utility.h".

From Corelib Require Import PrimString.
Crane Extract Inlined Constant PrimString.char63 => "char".
Crane Extract Inlined Constant PrimString.string => "bsl::string" From "bsl_string.h".
Crane Extract Inlined Constant PrimString.cat => "%a0 + %a1" From "bsl_string.h".
(* [get] is total in Rocq: [get_spec] defines [get s i = nth (to_nat i) s 0],
   so an out-of-range index yields the null char rather than undefined behavior.
   The bounds check reproduces that semantics exactly and prevents an
   out-of-bounds read of [bsl::string] (CWE-125). *)
Crane Extract Inlined Constant PrimString.get =>
  "((%a1 >= 0 && %a1 < static_cast<int64_t>(%a0.length())) ? %a0[%a1] : static_cast<char>(0))"
  From "bsl_string.h".
(* [sub] is total in Rocq (Pstring.sub): an [off] at or past the string's
   length yields the empty string rather than raising, and [len] is clamped
   to what remains. [bsl::string::substr] already clamps [count], but throws
   when [pos > size()]. The guard reproduces Rocq's clamp-to-empty behavior
   instead of letting the exception escape and terminate the generated
   program (CWE-248/CWE-755). *)
Crane Extract Inlined Constant PrimString.sub =>
  "((%a1 >= 0 && %a1 <= static_cast<int64_t>(%a0.length())) ? %a0.substr(%a1, %a2) : bsl::string())"
  From "bsl_string.h".
Crane Extract Inlined Constant PrimString.length => "%a0.length()" From "bsl_string.h".

(* int63 primitives - int64_t with 63-bit masking.
   Arithmetic is performed in the unsigned (uint64_t) domain, where overflow is
   defined as wraparound, then masked to [0, 2^63) to match Rocq semantics and
   cast back to int64_t. Performing add/sub/mul/shl directly on signed int64_t
   would be undefined behavior on overflow (CWE-190). div and mod guard against
   division by zero. Bitwise ops preserve the invariant (inputs have bit 63 = 0). *)
From Corelib Require Import PrimInt63.
Crane Extract Inlined Constant PrimInt63.int => "int64_t" From "bsl_cstdint.h".
Crane Extract Inlined Constant PrimInt63.add => "static_cast<int64_t>((static_cast<uint64_t>(%a0) + static_cast<uint64_t>(%a1)) & 0x7FFFFFFFFFFFFFFFULL)".
Crane Extract Inlined Constant PrimInt63.sub => "static_cast<int64_t>((static_cast<uint64_t>(%a0) - static_cast<uint64_t>(%a1)) & 0x7FFFFFFFFFFFFFFFULL)".
Crane Extract Inlined Constant PrimInt63.mul => "static_cast<int64_t>((static_cast<uint64_t>(%a0) * static_cast<uint64_t>(%a1)) & 0x7FFFFFFFFFFFFFFFULL)".
Crane Extract Inlined Constant PrimInt63.mod => "(%a1 == 0 ? 0 : %a0 % %a1)".
Crane Extract Inlined Constant PrimInt63.div => "(%a1 == 0 ? 0 : %a0 / %a1)".
Crane Extract Inlined Constant PrimInt63.eqb => "%a0 == %a1".
Crane Extract Inlined Constant PrimInt63.ltb => "%a0 < %a1".
Crane Extract Inlined Constant PrimInt63.leb => "%a0 <= %a1".
Crane Extract Inlined Constant PrimInt63.land => "(%a0 & %a1)".
Crane Extract Inlined Constant PrimInt63.lor => "(%a0 | %a1)".
Crane Extract Inlined Constant PrimInt63.lxor => "(%a0 ^ %a1)".
Crane Extract Inlined Constant PrimInt63.lsl => "(%a1 >= 63 ? 0 : static_cast<int64_t>((static_cast<uint64_t>(%a0) << %a1) & 0x7FFFFFFFFFFFFFFFULL))".
Crane Extract Inlined Constant PrimInt63.lsr => "(%a1 >= 63 ? 0 : static_cast<int64_t>(static_cast<uint64_t>(%a0) >> %a1))".

(* PrimFloat - IEEE 754 binary64 (C++ double). *)
From Corelib Require Import PrimFloat.
Crane Extract Inlined Constant PrimFloat.float => "double".
Crane Extract Inlined Constant PrimFloat.add => "(%a0 + %a1)".
Crane Extract Inlined Constant PrimFloat.sub => "(%a0 - %a1)".
Crane Extract Inlined Constant PrimFloat.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant PrimFloat.div => "(%a0 / %a1)".
Crane Extract Inlined Constant PrimFloat.opp => "(-%a0)".
Crane Extract Inlined Constant PrimFloat.abs => "bsl::abs(%a0)" From "bsl_cmath.h".
Crane Extract Inlined Constant PrimFloat.sqrt => "bsl::sqrt(%a0)" From "bsl_cmath.h".
Crane Extract Inlined Constant PrimFloat.eqb => "%a0 == %a1".
Crane Extract Inlined Constant PrimFloat.ltb => "%a0 < %a1".
Crane Extract Inlined Constant PrimFloat.leb => "%a0 <= %a1".
Crane Extract Inlined Constant PrimFloat.of_uint63 => "static_cast<double>(%a0)".
