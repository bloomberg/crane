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
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance envE_mapping (T : Type) : TypeMapping (envE T) :=
  event_family ["cstdlib"; "optional"; "string"]
    [event (Ref (@GetEnv)) "[&]() -> std::optional<std::string> {
  auto* v = std::getenv(%a0.c_str());
  return v ? std::optional<std::string>(v) : std::optional<std::string>();
}()";
     event (Ref (@SetEnv)) "setenv(%a0.c_str(), %a1.c_str(), 1)";
     event (Ref (@UnsetEnv)) "unsetenv(%a0.c_str())"].

#[export] Instance get_env_mapping : OperationMapping (Ref (@get_env)) :=
  effect_cpp ["cstdlib"; "optional"; "string"] ["name"]
    (Expr "[&]() -> std::optional<std::string> {
  auto* v = std::getenv(%arg(name).c_str());
  return v ? std::optional<std::string>(v) : std::optional<std::string>();
}()").
