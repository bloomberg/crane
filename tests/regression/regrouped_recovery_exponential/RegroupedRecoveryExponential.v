(** Found by Ephyra round 29 (open item of the round-28 fix of
    [id_any_cast_flat_fn]). A callable recovered from a box ([Datatypes.id]
    applied to a two-argument function) is regrouped to a curried slot
    ([twice] at [A := (nat -> nat) -> nat -> nat]). Fixed: the regrouping
    adapter re-evaluated the whole recovered expression, argument of [id]
    included, on every call, so the [let m := lvl d' in ...] that Rocq
    evaluates once per level was evaluated each time [twice] applied its
    function and [lvl d] made [2^d] calls instead of [d] (measured: [lvl 16]
    0.16 s, [lvl 22] 7.4 s, [lvl 40] did not finish). The regrouping now
    binds a value that is not a name or a closure once, where it is
    regrouped, and the adapter holds it by move. Expected and now:
    [lvl 40 = 2^40] immediately. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Module RegroupedRecoveryExponential.

Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).

Fixpoint lvl (d : nat) : nat :=
  match d with
  | 0 => 1
  | S d' =>
      twice (id (let m := lvl d' in fun (c : nat -> nat) (n : nat) => c n + m))
        (fun n : nat => n) 0
  end.

End RegroupedRecoveryExponential.

Crane Extraction "regrouped_recovery_exponential" RegroupedRecoveryExponential.
