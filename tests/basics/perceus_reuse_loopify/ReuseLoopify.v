(* Perceus reuse smoke test: linear map/rev over an owned cons list. *)
From Stdlib Require Import List.
Module R.

Inductive lst : Type :=
| Nil : lst
| Cons : nat -> lst -> lst.

Fixpoint map1 (f : nat -> nat) (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x xs => Cons (f x) (map1 f xs)
  end.

Fixpoint rev_append1 (l : lst) (acc : lst) : lst :=
  match l with
  | Nil => acc
  | Cons x xs => rev_append1 xs (Cons x acc)
  end.

Definition rev1 (l : lst) : lst := rev_append1 l Nil.

Fixpoint sum1 (l : lst) : nat :=
  match l with
  | Nil => 0
  | Cons x xs => x + sum1 xs
  end.

End R.

Require Crane.Extraction.
From Crane Require Import Mapping.NatIntStd.
Set Crane NonAtomicRc.
Set Crane Reuse.
Set Crane Loopify.
Crane Extraction "perceus_reuse_loopify" R.
