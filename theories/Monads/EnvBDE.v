(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Environment variable effects for the BDE flavor.

   Re-exports shared definitions from [EnvDefs.v] and adds C++ extraction
   mappings targeting BDE ([bsl::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.EnvDefs.

Crane Extract Inductive envE => ""
  [ "[&]() -> bsl::optional<bsl::string> {
  auto* v = std::getenv(%a0.c_str());
  return v ? bsl::optional<bsl::string>(v) : bsl::optional<bsl::string>();
}()"
    "setenv(%a0.c_str(), %a1.c_str(), 1)"
    "unsetenv(%a0.c_str())" ]
  From "cstdlib" "bsl_optional.h" "bsl_string.h".

Crane Extract Inlined Constant get_env =>
"[&]() -> bsl::optional<bsl::string> {
  auto* v = std::getenv(%a0.c_str());
  return v ? bsl::optional<bsl::string>(v) : bsl::optional<bsl::string>();
}()" From "cstdlib" "bsl_optional.h" "bsl_string.h".
