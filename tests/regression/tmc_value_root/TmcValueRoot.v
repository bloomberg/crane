From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Extraction.

Set Crane Loopify.

Module TmcValueRoot.

(** A list built in destination-passing style is assembled in place: its first
    node is the result itself, so only the cells below it are allocated, and
    an empty result allocates nothing. *)
Inductive lst := Nil | Cons (x : nat) (l : lst).

Fixpoint range (start count : nat) : lst :=
  match count with
  | O => Nil
  | S c => Cons start (range (S start) c)
  end.

Fixpoint app (xs ys : lst) : lst :=
  match xs with
  | Nil => ys
  | Cons x r => Cons x (app r ys)
  end.

(** Two cells per step: the second is allocated and linked into the first. *)
Fixpoint stutter (xs : lst) : lst :=
  match xs with
  | Nil => Nil
  | Cons x r => Cons x (Cons x (stutter r))
  end.

End TmcValueRoot.

Crane Extraction "tmc_value_root" TmcValueRoot.
