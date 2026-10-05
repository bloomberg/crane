From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.

Module CallbackStaysConcrete.

(** A callback the body only calls -- through a local fixpoint entered where
    it is written, or under a bind that is desugared into statements -- keeps
    its own type, and is passed by reference rather than erased into a
    [crane::fn]. *)
Fixpoint sum_map_acc (f : nat -> nat) (l : list nat) (acc : nat) : nat :=
  match l with nil => acc | x :: r => sum_map_acc f r (acc + f x) end.

Definition better_sum (f : nat -> nat) (l : list nat) : nat :=
  let fix go (l : list nat) (acc : nat) : nat :=
    match l with nil => acc | x :: r => go r (acc + f x) end
  in go l 0.

Definition apply_io (f : nat -> nat) (n : nat) : itree ioE nat :=
  x <- Ret n ;; Ret (f x).

End CallbackStaysConcrete.

Crane Extraction "callback_stays_concrete" CallbackStaysConcrete.
