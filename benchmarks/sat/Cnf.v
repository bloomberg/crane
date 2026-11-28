(** CNF formulas in the solver's encoding, and what it is to satisfy one.
    A formula is a list of clauses, a clause a list of literals; literal
    [2v] says variable [v] is true and [2v+1] that it is false. *)
From Stdlib Require Import List PeanoNat.
Require Import Solver.
Import Solver.

(** Literal [l] holds under the valuation [val]. *)
Definition lit_true (val : nat -> bool) (l : nat) : Prop := val (lvar l) = Nat.even l.

(** [val] makes some literal of every clause of [F] true. *)
Definition satisfies (val : nat -> bool) (F : list (list nat)) : Prop :=
  Forall (Exists (lit_true val)) F.

(** Every literal of [F] is below [lim]: with [lim = 2 * nvars], [F] only
    mentions the variables [0 .. nvars). *)
Definition lits_below (lim : nat) (F : list (list nat)) : Prop :=
  Forall (Forall (fun l => l < lim)) F.
