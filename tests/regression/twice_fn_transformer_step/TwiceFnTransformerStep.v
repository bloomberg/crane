(** Found by Ephyra round 25. Variant of [pick_curried_fn_overapply]: the
    function-typed argument of the outer [twice] is itself a call of [twice] at
    a function-transformer type, [A := (nat -> nat) -> nat -> nat]. Besides
    the eta-expansion of the variant, the inner call's template argument took
    the grouping of the outer slot, [twice<crane::fn<crane::fn<uint64_t
    (uint64_t)>(crane::fn<uint64_t(uint64_t)>)>>], while its step lambda,
    passed at a forwarding reference, was built flat at the instantiation,
    [crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)>] returning
    a two-argument lambda, so the step did not satisfy [twice]'s invocability
    constraint ("no matching function for call to 'twice'").

    Fixed: an argument passed at a forwarding reference is built at the
    grouping of its parameter at the type arguments the call writes, as an
    argument at a declared parameter already was
    ([Application.gen_call_args], [Calls.parameter_at_written]). *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.

Module TwiceFnTransformerStep.

Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).

Definition result : nat :=
  twice (twice (fun (_ : (nat -> nat) -> nat -> nat) (h : nat -> nat) (n : nat) => h (S n))
                (fun h => h)) (fun n => n * 10) 1.

End TwiceFnTransformerStep.

Crane Extraction "twice_fn_transformer_step" TwiceFnTransformerStep.
