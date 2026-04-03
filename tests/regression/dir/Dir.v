(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.Dir.

Open Scope itree_scope.

Module Dir.

  Definition make_dir (path : string) : itree dirE bool :=
    create_directory path.

  Definition remove_dir (path : string) : itree dirE bool :=
    remove_directory path.

  Definition get_cwd : itree dirE string := current_path.

  Definition list_dir (path : string) : itree dirE (list string) :=
    list_directory path.

End Dir.

Crane Extraction "dir" Dir.
