(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: keyword-safe emission for global symbol named class. *)

From Stdlib Require Import Nat.

Module KeywordClassGlobal.

Definition class (n : nat) : nat := n + n.
Definition t : nat := class 4.

End KeywordClassGlobal.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "keyword_class_global" KeywordClassGlobal.
