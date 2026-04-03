(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.TempFile.

Open Scope itree_scope.

Module TempFile.

  Definition make_temp_file (prefix : string) : itree tempFileE string :=
    create_temp_file prefix.

  Definition make_temp_dir (prefix : string) : itree tempFileE string :=
    create_temp_dir prefix.

End TempFile.

Crane Extraction "temp_file" TempFile.
