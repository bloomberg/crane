(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import List Bool.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd External.Vector Monads.ITree Monads.IO Monads.STM.
From Corelib Require Import PrimInt63.

Import ListNotations.
Import MonadNotations.
Set Implicit Arguments.

(* ==== Key type requirements ==== *)

Module SkipList.

Open Scope int63.

End SkipList.

Crane Extraction "skiplist" SkipList.