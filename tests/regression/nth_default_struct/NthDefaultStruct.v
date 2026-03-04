(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: nth/default-style module path escaping collision *)

From Stdlib Require Import Nat.

Module NthDefaultStruct.

Module A.
  Module Value'.
    Definition f (n : nat) : nat := n.
  End Value'.
End A.

Module B.
  Module Value_.
    Definition g (n : nat) : nat := S n.
  End Value_.
End B.

Definition t : nat := A.Value'.f 0 + B.Value_.g 0.
End NthDefaultStruct.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "nth_default_struct" NthDefaultStruct.