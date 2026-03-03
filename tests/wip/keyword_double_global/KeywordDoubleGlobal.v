(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Bug 8: keyword-safe emission for global symbol named double. *)

From Stdlib Require Import Nat.

Module KeywordDoubleGlobal.

Definition double (n : nat) : nat := n + n.
Definition t : nat := double 3.

End KeywordDoubleGlobal.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "keyword_double_global" KeywordDoubleGlobal.