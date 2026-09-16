(* Exists only to collide with [Compare.is_lt], which forces both files to be
   emitted as structs rather than flattened into the top level. *)
From Crane Require Extraction.

Definition is_lt (n : nat) : bool := Nat.ltb n 3.
