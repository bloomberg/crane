(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared IO effect definitions (flavor-independent).

   Contains the effect inductives ([consoleE], [fileE]), composed effect
   ([ioE]), and smart constructors that are identical across library flavors.
   Flavor files ([IO.v], [IOBDE.v]) re-export this module and add
   flavor-specific C++ extraction mappings.
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Monads.ITree.

(** Console IO on standard input and output. *)
Inductive consoleE : Type -> Type :=
(** Write a string with no newline. *)
| Print : string -> consoleE unit
(** Write a string and a newline. *)
| PrintEndline : string -> consoleE unit
(** Read one line, without its newline. *)
| GetLine : consoleE string.

(**
   Security note (CWE-22 / CWE-73).

   [fileE] grants raw host filesystem authority: the path argument of
   [ReadFile], [WriteFile], [AppendFile], [FileExists], and [RemoveFile] is
   passed through to the underlying C++ filesystem call verbatim, so an
   absolute path or a [..] traversal reaches whatever the generated process
   can access. This is intentional -- these are general-purpose filesystem
   effects with no single containment root, so path confinement is a policy
   only the *embedding application* can define.

   A program that exposes these effects to untrusted input MUST confine the
   path before calling the effect (canonicalize and check containment under an
   approved root, reject absolute paths and [..] where unsafe, and gate
   destructive operations). The mappings themselves only guarantee that a
   failed or malformed path degrades to a neutral result rather than crashing
   the process (see [IO.v]); they do NOT restrict which paths are reachable.
   For containment guarantees, use [tempFileE] (see [TempFileDefs.v]), whose
   mappings reduce the caller prefix to a single filename component under the
   system temporary directory.
*)
Inductive fileE : Type -> Type :=
(** The whole contents of a file. *)
| ReadFile : string -> fileE string
(** Replace a file's contents, creating it if needed. *)
| WriteFile : string -> string -> fileE unit
(** Append to a file, creating it if needed. *)
| AppendFile : string -> string -> fileE unit
(** Whether anything exists at the path. *)
| FileExists : string -> fileE bool
(** Delete the file at the path. *)
| RemoveFile : string -> fileE unit.

(** The usual IO events: console plus files.
    Only a Rocq abbreviation, never emitted. *)
Definition ioE := consoleE +' fileE.
Crane Extract Skip ioE.

(** Write [s] to standard output. *)
Definition print {E} `{consoleE -< E} (s : string) : itree E unit := embed (Print s).
(** Write [s] and a newline to standard output. *)
Definition print_endline {E} `{consoleE -< E} (s : string) : itree E unit := embed (PrintEndline s).
(** Read a line from standard input. *)
Definition get_line {E} `{consoleE -< E} : itree E string := embed GetLine.

(** The contents of the file at [path]. *)
Definition read {E} `{fileE -< E} (path : string) : itree E string := embed (ReadFile path).
(** Overwrite the file at [path] with [content]. *)
Definition write_file {E} `{fileE -< E} (path content : string) : itree E unit := embed (WriteFile path content).
(** Append [content] to the file at [path]. *)
Definition append_file {E} `{fileE -< E} (path content : string) : itree E unit := embed (AppendFile path content).
(** Whether [path] exists. *)
Definition file_exists {E} `{fileE -< E} (path : string) : itree E bool := embed (FileExists path).
(** Delete the file at [path]. *)
Definition remove_file {E} `{fileE -< E} (path : string) : itree E unit := embed (RemoveFile path).

