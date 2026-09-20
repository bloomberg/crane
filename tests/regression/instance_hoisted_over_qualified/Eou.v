From Crane Require Import Mapping.Std.

(* Only here to collide with [MemoryBytes.helper].  A file's definitions land
   at global scope unless a cross-file name collision forces them into a file
   struct, and the struct is what the bug needs. *)
Definition helper (n : nat) : nat := n.
