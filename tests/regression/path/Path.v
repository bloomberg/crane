(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.Path.

Open Scope itree_scope.

Module Path.

  Definition abs_path (p : string) : itree pathE string := absolute p.

  Definition canon_path (p : string) : itree pathE string := canonical p.

  Definition rel_path (p : string) : itree pathE string := relative p.

  Definition check_is_dir (p : string) : itree pathE bool := is_directory p.

  Definition check_is_file (p : string) : itree pathE bool := is_regular_file p.

End Path.

Crane Extraction "path" Path.
