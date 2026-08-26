(* WIP: non-uniform (nested) inductive: the recursive occurrence is at type nest (A*A); the emitted C++ template does not instantiate. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module NonUniformPairNest.
Inductive nest (A : Type) : Type := NZ : A -> nest A | NS : nest (A * A) -> nest A.
Arguments NZ {A} _.
Arguments NS {A} _.
Fixpoint size (A : Type) (n : nest A) : nat :=
  match n with NZ _ => 1 | NS m => 2 * size (A * A) m end.
Definition go : nat := size nat (NS (NZ (1, 2))).
End NonUniformPairNest.
Crane Extraction "non_uniform_pair_nest" NonUniformPairNest.
