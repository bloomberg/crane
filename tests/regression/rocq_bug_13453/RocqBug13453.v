(* Rocq bug #13453: extraction of primitive arrays *)

Require Crane.Extraction.

Module RocqBug13453.

Primitive array := #array_type.

Definition a : array nat := [| 0%nat | 0%nat |].

End RocqBug13453.

Crane Extraction "rocq_bug_13453" RocqBug13453.
