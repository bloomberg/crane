(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared directory effect definitions (flavor-independent).

   Contains the effect inductive ([dirE]) and smart constructors that are
   identical across library flavors. Flavor files ([Dir.v], [DirBDE.v])
   re-export this module and add flavor-specific C++ extraction mappings.
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Monads.ITree.

(**
   Security note (CWE-22 / CWE-73).

   [dirE] grants raw host filesystem authority: the path argument of
   [CreateDirectory], [RemoveDirectory], and [ListDirectory] is passed to the
   underlying C++ filesystem call verbatim, so an absolute path or a [..]
   traversal reaches whatever the generated process can access. In particular
   [RemoveDirectory] maps to a *recursive* delete, so an attacker-influenced
   path can remove an arbitrary directory tree. This is intentional -- these
   are general-purpose directory effects with no single containment root, so
   path confinement is a policy only the *embedding application* can define.

   A program that exposes these effects to untrusted input MUST confine the
   path before calling the effect (canonicalize and check containment under an
   approved root, reject absolute paths and [..] where unsafe) and should treat
   [RemoveDirectory] as an opt-in destructive operation. The mappings
   themselves only guarantee that a failed or malformed path degrades to a
   neutral result rather than crashing the process, and that [ListDirectory]
   caps the number of entries it materializes (see [Dir.v]); they do NOT
   restrict which paths are reachable.
*)
Inductive dirE : Type -> Type :=
(** Create a directory and any missing parents; [true] on success. *)
| CreateDirectory : string -> dirE bool
(** Remove a directory tree recursively; [true] on success. *)
| RemoveDirectory : string -> dirE bool
(** The entry names (not full paths) of a directory, in no particular order. *)
| ListDirectory : string -> dirE (list string)
(** The process's working directory. *)
| CurrentPath : dirE string.

(** Create [path] with its missing parents. *)
Definition create_directory {E} `{dirE -< E} (path : string) : itree E bool :=
  embed (CreateDirectory path).
(** Recursively delete [path]; see the security note on [dirE]. *)
Definition remove_directory {E} `{dirE -< E} (path : string) : itree E bool :=
  embed (RemoveDirectory path).
(** The entry names of the directory [path]. *)
Definition list_directory {E} `{dirE -< E} (path : string) : itree E (list string) :=
  embed (ListDirectory path).
(** The working directory. *)
Definition current_path {E} `{dirE -< E} : itree E string :=
  embed CurrentPath.
