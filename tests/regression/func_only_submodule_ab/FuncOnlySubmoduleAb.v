(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: function-only nested submodules emit wrappers correctly. *)

From Stdlib Require Import Nat.

Module FuncOnlySubmoduleAb.

Module Root.
  Module A.
    Definition inc (n : nat) : nat := S n.
  End A.
  Module B.
    Definition dec (n : nat) : nat := Nat.pred n.
  End B.
End Root.

Definition t : nat := Root.A.inc (Root.B.dec 3).

End FuncOnlySubmoduleAb.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "func_only_submodule_ab" FuncOnlySubmoduleAb.
