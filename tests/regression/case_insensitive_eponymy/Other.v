(* Exists only to collide with [CFG.size], which forces both files to be
   emitted as structs rather than flattened into the top level. *)
From Crane Require Extraction.

Definition size (n : nat) : nat := S n.
