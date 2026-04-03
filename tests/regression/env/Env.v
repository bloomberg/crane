(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.Env.

Open Scope itree_scope.

Module Env.

  Definition set_and_get (name value : string) : itree envE (option string) :=
    set_env name value ;;
    get_env name.

  Definition set_unset_get (name value : string) : itree envE (option string) :=
    set_env name value ;;
    unset_env name ;;
    get_env name.

  Definition get_missing (name : string) : itree envE (option string) :=
    get_env name.

End Env.

Crane Extraction "env" Env.
