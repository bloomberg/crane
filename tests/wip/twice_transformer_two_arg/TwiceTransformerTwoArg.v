(** Found by Ephyra round 28. Variant of round 25's
    [twice_fn_transformer_step] (fixed): the same nested [twice] whose step
    transforms function transformers, but over a two-argument function,
    [A := (bool -> nat -> nat) -> bool -> nat -> nat]. The inner [twice]'s
    template argument spells the transformer over the flat
    [crane::fn<uint64_t(bool, uint64_t)>], and the step's call of its first
    parameter [k h b n] does not match it; the outer [twice] call is not
    viable either. Over one-argument [nat -> nat] (the fixed test's shape)
    it compiles. Under CRANE_CHECK_IR: "Crane IR check (variable read binder
    type): a read for call arity in ...: lowering's binder is
    fn(fn(bool,nat)->nat)->...". Expected: compiles, [result = 22]. Actual:
    "no matching function for call to object of type 'const
    crane::fn<crane::fn<unsigned long long (bool, unsigned long long)>
    (crane::fn<unsigned long long (bool, unsigned long long)>)>'" and "no
    matching function for call to 'twice'". *)
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
