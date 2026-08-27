From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** A constructor field holding the inductive under an [option]
    ([N : option c -> c]) is stored as [shared_ptr<optional<c>>].  The pattern
    match must dereference the pointer before testing [has_value()]. *)

Module RecursiveUnderOption.
Inductive c : Type := N : option c -> c.
Fixpoint build (n : nat) : c :=
  match n with O => N None | S m => N (Some (build m)) end.
Fixpoint depth (x : c) : nat :=
  match x with N None => 0 | N (Some y) => S (depth y) end.
Definition go : nat := depth (build 1000).
End RecursiveUnderOption.
Crane Extraction "recursive_under_option" RecursiveUnderOption.
