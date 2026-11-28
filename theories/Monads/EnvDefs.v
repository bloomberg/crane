(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared environment variable effect definitions (flavor-independent).

   Contains the effect inductive ([envE]) and smart constructors that are
   identical across library flavors. Flavor files ([Env.v], [EnvBDE.v])
   re-export this module and add flavor-specific C++ extraction mappings.

   [set_env] and [unset_env] use POSIX calls that are the same in both
   flavors, so their extraction mappings live here.
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Monads.ITree.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** Process environment variables. *)
Inductive envE : Type -> Type :=
(** Look a variable up; [None] when it is unset. *)
| GetEnv : string -> envE (option string)
(** Set a variable, overwriting any existing value. *)
| SetEnv : string -> string -> envE unit
(** Remove a variable. *)
| UnsetEnv : string -> envE unit.

(** Read the variable [name], [None] when unset. *)
Definition get_env {E} `{envE -< E} (name : string) : itree E (option string) :=
  embed (GetEnv name).
(** Bind [name] to [value] in the process environment. *)
Definition set_env {E} `{envE -< E} (name value : string) : itree E unit :=
  embed (SetEnv name value).
(** Remove [name] from the process environment. *)
Definition unset_env {E} `{envE -< E} (name : string) : itree E unit :=
  embed (UnsetEnv name).

(** [set_env] is POSIX [setenv] with overwrite on. *)
#[export] Instance set_env_mapping : OperationMapping (Ref (@set_env)) :=
  effect_cpp ["cstdlib"] ["name"; "value"]
    (Structured (Call "setenv" [] [Method (Arg "name") "c_str" []; Method (Arg "value") "c_str" []; lit 1])).

(** [unset_env] is POSIX [unsetenv]. *)
#[export] Instance unset_env_mapping : OperationMapping (Ref (@unset_env)) :=
  effect_cpp ["cstdlib"] ["name"]
    (Structured (Call "unsetenv" [] [Method (Arg "name") "c_str" []])).
