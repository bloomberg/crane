(** Found by Ephyra round 29 (open item of the round-28 fix of
    [id_any_cast_flat_fn]). When a callable recovered from a box
    ([Datatypes.id] applied to a two-argument function) is regrouped to a
    curried slot ([twice] at [A := (nat -> nat) -> nat -> nat]), the
    regrouping lambda re-evaluates the whole recovered expression, argument
    of [id] included, on every call: the [let m := lvl d' in ...] that Rocq
    evaluates once per level is evaluated each time [twice] applies its
    function, so [lvl d] makes [2^d] calls instead of [d]. The value is
    right; the cost is exponential (measured: [lvl 16] 0.16 s, [lvl 18]
    0.50 s, [lvl 20] 1.9 s, [lvl 22] 7.4 s). Expected: [lvl 40 = 2^40]
    immediately. Actual: does not finish (the test aborts after 20 s). *)
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
