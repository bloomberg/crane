(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Standard library extraction for string views ([std::string_view]). *)
From Crane Require Extraction.
From Crane Require Export External.StringViewDefs.

Crane Extract Inlined Constant string_view => "std::basic_string_view<char>" From "string_view".
Crane Extract Inlined Constant empty => "%a0.empty()" From "string_view".
Crane Extract Inlined Constant sv_eq => "%a0 == %a1" From "string_view".
Crane Extract Inlined Constant length => "%a0.length()" From "string_view".
Crane Extract Inlined Constant substr => "%a0.substr(%a1, %a2)" From "string_view".
Crane Extract Inlined Constant sv_of_string => "{%a0.data(), %a0.size()}" From "string_view".
Crane Extract Inlined Constant contains => "%a0.contains(%a1)" From "string_view".
Crane Extract Inlined Constant sv_get => "%a0[%a1]" From "string_view".
Crane Extract Inlined Constant sv_at => "%a0.at(%a1)" From "string_view".
Crane Extract Inlined Constant empty_sv => "std::string_view(nullptr, 0)" From "string_view".
