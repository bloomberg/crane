From Stdlib Require Import Nat.
Require Crane.Extraction.

Module RApply.

(* Record containing a function. Includes extra field to avoid
   singleton-record special case. *)
Record R : Type := { f : nat -> nat -> nat; _tag : nat }.

(* Destruct record and apply function inside to two arguments. *)
Definition apply_record (r : R) (a b : nat) : nat :=
  match r with
  | {| f := g; _tag := _ |} => g a b
  end.

End RApply.
Crane Extraction "rapply" RApply.
