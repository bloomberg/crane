(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 2: wrapper declaration overwrite instead of merge for shared wrapper target. *)

From Stdlib Require Import Nat.

Module WrapperDeclMerge.

Module A.
  Module Nat.
    Definition fa (n : nat) : nat := n.
  End Nat.
End A.

Module B.
  Module Nat.
    Definition fb (n : nat) : nat := S n.
  End Nat.
End B.

Definition x : nat := A.Nat.fa 4.
Definition y : nat := B.Nat.fb 4.

End WrapperDeclMerge.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "wrapper_decl_merge" WrapperDeclMerge.