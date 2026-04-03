(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Environment variable effects for the standard library flavor.

   Re-exports shared definitions from [EnvDefs.v] and adds C++ extraction
   mappings targeting the standard library ([std::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export Monads.EnvDefs.

Crane Extract Inductive envE => ""
  [ "[&]() -> std::optional<std::string> {
  auto* v = std::getenv(%a0.c_str());
  return v ? std::optional<std::string>(v) : std::optional<std::string>();
}()"
    "setenv(%a0.c_str(), %a1.c_str(), 1)"
    "unsetenv(%a0.c_str())" ]
  From "cstdlib" "optional" "string".

Crane Extract Inlined Constant get_env =>
"[&]() -> std::optional<std::string> {
  auto* v = std::getenv(%a0.c_str());
  return v ? std::optional<std::string>(v) : std::optional<std::string>();
}()" From "cstdlib" "optional" "string".
