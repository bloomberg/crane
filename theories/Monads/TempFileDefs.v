(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Shared temporary file effect definitions (flavor-independent).

   Contains the effect inductive ([tempFileE]) and smart constructors that
   are identical across library flavors. Flavor files ([TempFile.v],
   [TempFileBDE.v]) re-export this module and add flavor-specific C++
   extraction mappings.
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Monads.ITree.

(** Fresh entries in the system temporary
    directory, named after a caller prefix. *)
Inductive tempFileE : Type -> Type :=
(** Create an empty temporary file and return its path. *)
| CreateTempFile : string -> tempFileE string
(** Create an empty temporary directory and return its path. *)
| CreateTempDir : string -> tempFileE string.

(** A new empty file whose name starts with [prefix]. *)
Definition create_temp_file {E} `{tempFileE -< E} (prefix : string)
  : itree E string := embed (CreateTempFile prefix).
(** A new empty directory whose name starts with [prefix]. *)
Definition create_temp_dir {E} `{tempFileE -< E} (prefix : string)
  : itree E string := embed (CreateTempDir prefix).
