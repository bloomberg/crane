(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Standard-library extraction mappings.

    Maps [option], [prod], [string], [int63], and [float] to their
    C++ standard library equivalents ([std::optional], [std::pair],
    [std::string], [int64_t], [double]): [StdCore] and the legacy string
    mappings ([StringView] maps strings as a typed mapping with a
    [std::string_view] read view instead).

    Sets the stdlib flavor to ["std"]. *)
From Crane Require Extraction.
From Crane Require Export Mapping.StdCore.

From Corelib Require Import PrimString.
Crane Extract Inlined Constant PrimString.string => "std::string" From "string".
Crane Extract Inlined Constant PrimString.cat => "%a0 + %a1" From "string".
(* [get] is total in Rocq: [get_spec] defines [get s i = nth (to_nat i) s 0],
   so an out-of-range index yields the null char rather than undefined behavior.
   The bounds check reproduces that semantics exactly and prevents an
   out-of-bounds read of [std::string] (CWE-125). *)
Crane Extract Inlined Constant PrimString.get =>
  "((%a1 >= 0 && %a1 < static_cast<int64_t>(%a0.length())) ? %a0[%a1] : static_cast<char>(0))"
  From "string".
(* [sub] is total in Rocq (Pstring.sub): an [off] at or past the string's
   length yields the empty string rather than raising, and [len] is clamped
   to what remains. [std::string::substr] already clamps [count], but throws
   [std::out_of_range] when [pos > size()]. The guard reproduces Rocq's
   clamp-to-empty behavior instead of letting the exception escape and
   terminate the generated program (CWE-248/CWE-755). *)
Crane Extract Inlined Constant PrimString.sub =>
  "((%a1 >= 0 && %a1 <= static_cast<int64_t>(%a0.length())) ? %a0.substr(%a1, %a2) : std::string())"
  From "string".
Crane Extract Inlined Constant PrimString.length => "static_cast<int64_t>(%a0.length())" From "string".

