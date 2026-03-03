(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 3: missing wrapper emission for function-only nested submodule. *)

From Stdlib Require Import Nat.

Module FuncOnlySubmodule.

Module Outer.
  Module Inner.
    Definition bump (n : nat) : nat := S n.
  End Inner.
End Outer.

Definition t : nat := Outer.Inner.bump 0.

End FuncOnlySubmodule.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "func_only_submodule" FuncOnlySubmodule.