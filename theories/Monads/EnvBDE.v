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
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance envE_mapping (T : Type) : TypeMapping (envE T) :=
  event_family ["cstdlib"; "bsl_optional.h"; "bsl_string.h"]
    [event (Ref (@GetEnv)) "[&]() -> bsl::optional<bsl::string> {
  auto* v = std::getenv(%a0.c_str());
  return v ? bsl::optional<bsl::string>(v) : bsl::optional<bsl::string>();
}()";
     event (Ref (@SetEnv)) "setenv(%a0.c_str(), %a1.c_str(), 1)";
     event (Ref (@UnsetEnv)) "unsetenv(%a0.c_str())"].

#[export] Instance get_env_mapping : OperationMapping (Ref (@get_env)) :=
  effect_cpp ["cstdlib"; "bsl_optional.h"; "bsl_string.h"] ["name"]
    (Expr "[&]() -> bsl::optional<bsl::string> {
  auto* v = std::getenv(%arg(name).c_str());
  return v ? bsl::optional<bsl::string>(v) : bsl::optional<bsl::string>();
}()").
