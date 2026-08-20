From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A rose tree whose recursive occurrence sits inside [list rose].

    The generated iterative destructor for [rose] drains the [list rose] child
    by walking the cons spine and moving each element out.  The [use_count]
    ownership check only covers the head cell, so destroying one [rose] guts a
    list suffix that is still shared with another live value. *)

Module RoseSharedSuffixDrain.

Inductive rose : Type := Node : nat -> list rose -> rose.

Fixpoint rsum (t : rose) : nat :=
  match t with
  | Node v cs =>
      v + (fix go (l : list rose) : nat :=
             match l with
             | [] => 0
             | c :: r => rsum c + go r
             end) cs
  end.

(** [t] is shared between two roses.  The first one is a temporary whose
    destructor runs before [b] is computed. *)
Definition run (n : nat) : nat :=
  let t := [Node n []; Node (S n) []; Node (S (S n)) []] in
  let a := rsum (Node 1 t) in
  let b := rsum (Node 2 t) in
  a + b.

End RoseSharedSuffixDrain.

Crane Extraction "rose_shared_suffix_drain" RoseSharedSuffixDrain.
