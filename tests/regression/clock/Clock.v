(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.Std Monads.ITree Monads.Clock.

Open Scope itree_scope.

Module Clock.

  Definition get_steady : itree clockE int := steady_now.

  Definition get_system : itree clockE int := system_now.

  Definition get_time : itree clockE int := now.

  Definition elapsed : itree clockE int :=
    t1 <- steady_now ;;
    t2 <- steady_now ;;
    Ret (sub t2 t1).

End Clock.

Crane Extraction "clock" Clock.
