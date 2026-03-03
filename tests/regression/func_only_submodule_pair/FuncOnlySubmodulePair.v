(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: function-only nested submodules remain emitted consistently. *)

From Stdlib Require Import Nat.

Module FuncOnlySubmodulePair.

Module Outer.
  Module A.
    Definition inc (n : nat) : nat := S n.
  End A.
  Module B.
    Definition dec (n : nat) : nat := Nat.pred n.
  End B.
End Outer.

Definition t : nat := Outer.A.inc (Outer.B.dec 3).

End FuncOnlySubmodulePair.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "func_only_submodule_pair" FuncOnlySubmodulePair.
