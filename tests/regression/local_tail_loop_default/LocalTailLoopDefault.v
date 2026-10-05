From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module LocalTailLoopDefault.

(** A tail-recursive local fixpoint becomes a loop without [Crane Loopify]:
    its call depth is bounded however long the input, and it is an ordinary
    lambda rather than a self-applying one. *)
Definition sum_to (n : nat) : nat :=
  let fix go (k acc : nat) : nat :=
    match k with O => acc | S k' => go k' (acc + k) end
  in go n 0.

(** The accumulator is an owned loop variable, rebuilt on every step. *)
Definition rev_map (f : nat -> nat) (l : list nat) : list nat :=
  let fix go (l : list nat) (acc : list nat) : list nat :=
    match l with [] => acc | x :: r => go r (f x :: acc) end
  in go l [].

End LocalTailLoopDefault.

Crane Extraction "local_tail_loop_default" LocalTailLoopDefault.
