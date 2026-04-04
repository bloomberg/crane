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

Inductive consoleE : Type -> Type :=
| Print : string -> consoleE unit
| PrintEndline : string -> consoleE unit
| GetLine : consoleE string.

Inductive fileE : Type -> Type :=
| ReadFile : string -> fileE string
| WriteFile : string -> string -> fileE unit
| AppendFile : string -> string -> fileE unit
| FileExists : string -> fileE bool
| RemoveFile : string -> fileE unit.

Definition ioE := consoleE +' fileE.
Crane Extract Skip ioE.

Definition print {E} `{consoleE -< E} (s : string) : itree E unit := embed (Print s).
Definition print_endline {E} `{consoleE -< E} (s : string) : itree E unit := embed (PrintEndline s).
Definition get_line {E} `{consoleE -< E} : itree E string := embed GetLine.

Definition read {E} `{fileE -< E} (path : string) : itree E string := embed (ReadFile path).
Definition write_file {E} `{fileE -< E} (path content : string) : itree E unit := embed (WriteFile path content).
Definition append_file {E} `{fileE -< E} (path content : string) : itree E unit := embed (AppendFile path content).
Definition file_exists {E} `{fileE -< E} (path : string) : itree E bool := embed (FileExists path).
Definition remove_file {E} `{fileE -< E} (path : string) : itree E unit := embed (RemoveFile path).

