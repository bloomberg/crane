From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** WIP: A constructor field holding the inductive under a pair
    (`N : (nat * c) -> c`) is stored as `shared_ptr<pair<uint64_t, c>>` but the
    generated code reads `.second` off the pointer. *)

Module RecursiveUnderPair.
Inductive c : Type := Stop : c | N : (nat * c)%type -> c.
Fixpoint build (n : nat) : c :=
  match n with O => Stop | S m => N (n, build m) end.
Fixpoint depth (x : c) : nat :=
  match x with Stop => 0 | N p => S (depth (snd p)) end.
Definition go : nat := depth (build 1000).
End RecursiveUnderPair.
Crane Extraction "recursive_under_pair" RecursiveUnderPair.
