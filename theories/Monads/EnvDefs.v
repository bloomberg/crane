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

Inductive envE : Type -> Type :=
| GetEnv : string -> envE (option string)
| SetEnv : string -> string -> envE unit
| UnsetEnv : string -> envE unit.

Definition get_env {E} `{envE -< E} (name : string) : itree E (option string) :=
  embed (GetEnv name).
Definition set_env {E} `{envE -< E} (name value : string) : itree E unit :=
  embed (SetEnv name value).
Definition unset_env {E} `{envE -< E} (name : string) : itree E unit :=
  embed (UnsetEnv name).

Crane Extract Inlined Constant set_env =>
  "setenv(%a0.c_str(), %a1.c_str(), 1)" From "cstdlib".

Crane Extract Inlined Constant unset_env =>
  "unsetenv(%a0.c_str())" From "cstdlib".
