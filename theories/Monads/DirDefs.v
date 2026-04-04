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

Inductive dirE : Type -> Type :=
| CreateDirectory : string -> dirE bool
| RemoveDirectory : string -> dirE bool
| ListDirectory : string -> dirE (list string)
| CurrentPath : dirE string.

Definition create_directory {E} `{dirE -< E} (path : string) : itree E bool :=
  embed (CreateDirectory path).
Definition remove_directory {E} `{dirE -< E} (path : string) : itree E bool :=
  embed (RemoveDirectory path).
Definition list_directory {E} `{dirE -< E} (path : string) : itree E (list string) :=
  embed (ListDirectory path).
Definition current_path {E} `{dirE -< E} : itree E string :=
  embed CurrentPath.
