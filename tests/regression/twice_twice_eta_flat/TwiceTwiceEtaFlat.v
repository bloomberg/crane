(** Found by Ephyra round 28. [twice] passed unapplied as [twice]'s step,
    [twice twice g], the result itself the step of an outer [twice], at
    [A := (nat -> nat) -> nat -> nat]. The unapplied [twice] was
    eta-expanded to a lambda taking [_ec0] at the flat
    [crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)>] and
    returning a flat two-argument lambda, while the inner [twice]'s template
    argument was the curried
    [crane::fn<crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>];
    inside, [twice<crane::fn<uint64_t(uint64_t)>>(_ec0, _ec1)] did not match
    either ("no matching function for call to 'twice'").

    Fixed: a global named as a value is compared with its slot at the call's
    grouping ([Calls.argument_position]), and its eta adapter takes the
    parameters its declaration groups, at the type arguments its use
    writes ([Coerce.declared_cpp], [Types.spell_as_declared]):
    [twice]'s step as [crane::fn<F(F)>], not two arguments in one group. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TwiceTwiceEtaFlat.

Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition result : nat :=
  twice (twice twice (fun (h : nat -> nat) (n : nat) => h n + 1)) (fun n : nat => n) 0.

End TwiceTwiceEtaFlat.

Crane Extraction "twice_twice_eta_flat" TwiceTwiceEtaFlat.
