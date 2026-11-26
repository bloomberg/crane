(** Found by Ephyra round 28. Variant of round 25's
    [twice_fn_transformer_step]: the same nested [twice] whose step
    transforms function transformers, but over a two-argument function,
    [A := (bool -> nat -> nat) -> bool -> nat -> nat]. The inner [twice]'s
    template argument spelled the transformer over the flat
    [crane::fn<uint64_t(bool, uint64_t)>], and lowering bound the step's
    first parameter [k] at it, but the representation plan, which planned
    the lambda's binders against the Core instantiation, gave [k] the flat
    three-argument type: [k h b n] was called [k(h, b, n)] ("no matching
    function for call to object of type ..."; under CRANE_CHECK_IR,
    "variable read binder type").

    Fixed: the representation plan plans a lambda passed to a global at its
    parameter at the call's grouping ([Calls.grouped_instantiation]), the
    position of a call nested in another's argument being that argument's
    parameter at the outer call's grouping ([Representation_plan.region]),
    as lowering builds it. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TwiceTransformerTwoArg.

Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition result : nat :=
  twice (twice (fun (k : (bool -> nat -> nat) -> bool -> nat -> nat) (h : bool -> nat -> nat) (b : bool) (n : nat) => k h b n + 1)
               (fun (h : bool -> nat -> nat) (b : bool) (n : nat) => h b n * 2))
    (fun (_ : bool) (n : nat) => n) true 4.

End TwiceTransformerTwoArg.

Crane Extraction "twice_transformer_two_arg" TwiceTransformerTwoArg.
