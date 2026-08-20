From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** Same underlying defect as [rose_shared_suffix_drain], reached with a
    different consumer and three successive sharers of the same spine: the
    generated [~rose()] drains the [list rose] child cell by cell, checking
    ownership only on the head [shared_ptr], so the shared tail cells are
    left moved-from for the next reader. *)

Module RoseSharedSuffixDrainSize.

Inductive rose : Type := Node : nat -> list rose -> rose.

Fixpoint rsize (t : rose) : nat :=
  match t with
  | Node _ cs =>
      S ((fix go (l : list rose) : nat :=
            match l with
            | [] => 0
            | c :: r => rsize c + go r
            end) cs)
  end.

Definition run (n : nat) : nat :=
  let t := [Node n []; Node (S n) []; Node (S (S n)) []; Node n []] in
  let a := rsize (Node 1 t) in
  let b := rsize (Node 2 t) in
  let c := rsize (Node 3 t) in
  a + b + c.

End RoseSharedSuffixDrainSize.

Crane Extraction "rose_shared_suffix_drain_size" RoseSharedSuffixDrainSize.
