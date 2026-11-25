(** Found by Ephyra round 25. Variant of [pick_curried_fn_overapply]: the
    function-typed argument of the outer [twice] is itself a call of [twice] at
    a function-transformer type, [A := (nat -> nat) -> nat -> nat]. Crane
    eta-expands it and over-applies the inner call's result to both binders,
    as in the variant, and in addition the inner call's template argument is
    spelled curried, [twice<crane::fn<crane::fn<uint64_t(uint64_t)>
    (crane::fn<uint64_t(uint64_t)>)>>], while the step lambda's binder is
    spelled flat, [crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>,
    uint64_t)>], and it returns a two-argument lambda, so the step does not
    satisfy [twice]'s invocability constraint. Without the outer [twice] the
    same step is spelled flat throughout and works.
    Expected: compiles, [result = 30]. Actual: "no matching function for call
    to 'twice'" (constraints not satisfied). *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TwiceFnTransformerStep.

Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).

Definition result : nat :=
  twice (twice (fun (_ : (nat -> nat) -> nat -> nat) (h : nat -> nat) (n : nat) => h (S n))
                (fun h => h)) (fun n => n * 10) 1.

End TwiceFnTransformerStep.

Crane Extraction "twice_fn_transformer_step" TwiceFnTransformerStep.
