(* WIP: user identifiers named uint64_t collide with the C++ type name from the nat mapping. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module IdentNamedUint64.
Inductive t : Type := uint64_t_ : nat -> t.
Definition uint64_t (n : nat) : nat := n.
Definition go : nat := uint64_t 1 + match uint64_t_ 2 with uint64_t_ n => n end.
End IdentNamedUint64.
Crane Extraction "ident_named_uint64" IdentNamedUint64.
