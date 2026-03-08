(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Nat.
From Crane Require Import Mapping.NatIntStd.
Module RecordApply.

(* Record containing a function. Includes extra field to avoid
   singleton-record special case. *)
Record R : Type := { f : nat -> nat -> nat; _tag : nat }.

(* Destruct record and apply function inside to two arguments. *)
Definition apply_record (r : R) (a b : nat) : nat :=
  match r with
  | {| f := g; _tag := _ |} => g a b
  end.

Definition r : R := {| f := (fun x y => x); _tag := 3|}.

Definition three : nat := r.(f) 3 0.

End RecordApply.

From Crane Require Extraction.
Crane Extraction "record_apply" RecordApply.
