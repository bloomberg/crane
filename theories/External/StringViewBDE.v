(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** BDE extraction for string views ([bsl::string_view]). *)
From Crane Require Extraction.
From Crane Require Export External.StringViewDefs.

Crane Extract Inlined Constant string_view => "bsl::basic_string_view<char>" From "bsl_string_view.h".
Crane Extract Inlined Constant empty => "%a0.empty()" From "bsl_string_view.h".
Crane Extract Inlined Constant sv_eq => "%a0 == %a1" From "bsl_string_view.h".
Crane Extract Inlined Constant length => "%a0.length()" From "bsl_string_view.h".
Crane Extract Inlined Constant substr => "%a0.substr(%a1, %a2)" From "bsl_string_view.h".
Crane Extract Inlined Constant sv_of_string => "{%a0.data(), %a0.size()}" From "bsl_string_view.h".
Crane Extract Inlined Constant contains => "%a0.contains(%a1)" From "bsl_string_view.h".
(* The [sv_get] axioms (StringViewDefs.v) constrain only in-range indices, so
   returning the null char for an out-of-range index is consistent with the
   specification and makes the operation total. The bounds check prevents an
   out-of-bounds read of a possibly non-owning [bsl::string_view] (CWE-125).
   Use [sv_at] when a throwing, checked accessor is desired instead. *)
Crane Extract Inlined Constant sv_get =>
  "((%a1 >= 0 && %a1 < static_cast<int64_t>(%a0.length())) ? %a0[%a1] : static_cast<char>(0))"
  From "bsl_string_view.h".
Crane Extract Inlined Constant sv_at => "%a0.at(%a1)" From "bsl_string_view.h".
Crane Extract Inlined Constant empty_sv => "bsl::string_view(nullptr, 0)" From "bsl_string_view.h".
