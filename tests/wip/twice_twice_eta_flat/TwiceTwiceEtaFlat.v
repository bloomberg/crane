(** Found by Ephyra round 28. [twice] passed unapplied as [twice]'s step,
    [twice twice g], the result itself the step of an outer [twice], at
    [A := (nat -> nat) -> nat -> nat]. The unapplied [twice] is eta-expanded
    to a lambda taking [_ec0] at the flat
    [crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)>] and
    returning a flat two-argument lambda, while the inner [twice]'s template
    argument is the curried
    [crane::fn<crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>];
    inside, [twice<crane::fn<uint64_t(uint64_t)>>(_ec0, _ec1)] does not match
    either. Kin of round 25's [twice_fn_transformer_step] (fixed) and of
    [nested_curried_instantiation]. Expected: compiles, [result = 8].
    Actual: "no matching function for call to 'twice'". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TwiceTwiceEtaFlat.

Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition result : nat :=
  twice (twice twice (fun (h : nat -> nat) (n : nat) => h n + 1)) (fun n : nat => n) 0.

End TwiceTwiceEtaFlat.

Crane Extraction "twice_twice_eta_flat" TwiceTwiceEtaFlat.
