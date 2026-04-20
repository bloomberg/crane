(* Rocq bug #10796: extraction inside a module *)

Require Crane.Extraction.
From Crane Require Import Mapping.NatIntStd.

Module RocqBug10796.

Definition a : nat := 0.

End RocqBug10796.

Crane Extraction "rocq_bug_10796" RocqBug10796.
