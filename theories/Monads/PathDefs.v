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

(** Filesystem path queries: normalization and file-type tests. *)
Inductive pathE : Type -> Type :=
(** The absolute path with symlinks, [.] and [..] resolved; the path must exist. *)
| Canonical : string -> pathE string
(** The path relative to the working directory. *)
| Relative : string -> pathE string
(** The path made absolute against the working
    directory, without touching the filesystem. *)
| Absolute : string -> pathE string
(** Whether the path names a directory. *)
| IsDirectory : string -> pathE bool
(** Whether the path names a regular file. *)
| IsRegularFile : string -> pathE bool.

(** Resolve [path] to its canonical absolute form. *)
Definition canonical {E} `{pathE -< E} (path : string) : itree E string :=
  embed (Canonical path).
(** [path] relative to the working directory. *)
Definition relative {E} `{pathE -< E} (path : string) : itree E string :=
  embed (Relative path).
(** [path] made absolute. *)
Definition absolute {E} `{pathE -< E} (path : string) : itree E string :=
  embed (Absolute path).
(** Whether [path] is a directory. *)
Definition is_directory {E} `{pathE -< E} (path : string) : itree E bool :=
  embed (IsDirectory path).
(** Whether [path] is a regular file. *)
Definition is_regular_file {E} `{pathE -< E} (path : string) : itree E bool :=
  embed (IsRegularFile path).
