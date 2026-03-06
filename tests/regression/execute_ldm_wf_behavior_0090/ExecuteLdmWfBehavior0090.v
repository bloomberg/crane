(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: ISZ iteration metric returns 16 at zero. *)

From Stdlib Require Import Nat.

Module ExecuteLdmWfBehavior0090.

Definition isz_iterations (v : nat) : nat :=
  if v =? 0 then 16 else 16 - v.

Definition t : nat := isz_iterations 12.

End ExecuteLdmWfBehavior0090.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "execute_ldm_wf_behavior_0090" ExecuteLdmWfBehavior0090.
