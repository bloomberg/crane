(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared filesystem path effect definitions (flavor-independent).

   Contains the effect inductive ([pathE]) and smart constructors that are
   identical across library flavors. Flavor files ([Path.v], [PathBDE.v])
   re-export this module and add flavor-specific C++ extraction mappings.

   For checking path existence, use [file_exists] from [fileE] (in [IODefs.v]).
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Monads.ITree.

Inductive pathE : Type -> Type :=
| Canonical : string -> pathE string
| Relative : string -> pathE string
| Absolute : string -> pathE string
| IsDirectory : string -> pathE bool
| IsRegularFile : string -> pathE bool.

Definition canonical {E} `{pathE -< E} (path : string) : itree E string :=
  embed (Canonical path).
Definition relative {E} `{pathE -< E} (path : string) : itree E string :=
  embed (Relative path).
Definition absolute {E} `{pathE -< E} (path : string) : itree E string :=
  embed (Absolute path).
Definition is_directory {E} `{pathE -< E} (path : string) : itree E bool :=
  embed (IsDirectory path).
Definition is_regular_file {E} `{pathE -< E} (path : string) : itree E bool :=
  embed (IsRegularFile path).
