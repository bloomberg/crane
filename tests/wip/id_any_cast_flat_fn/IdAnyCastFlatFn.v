(** Found by Ephyra round 28. [Datatypes.id] (whose type is the alias
    [ID := forall A, A -> A], so its argument and result are erased to
    [std::any]) applied to a two-argument function transformer, the result
    the step of [twice] at [A := (nat -> nat) -> nat -> nat]. The result is
    cast back with [crane::any_cast] to the flat
    [crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)>], while
    [twice]'s template argument wants the curried
    [crane::fn<crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>].
    A user-defined [myid {A} (x : A) := x] in the same place compiles, and so
    does [id step] applied directly. Under CRANE_CHECK_IR: "Crane IR check
    (coercion position): a coercion ... is lowered against
    fn(fn(nat)->nat)->fn(nat)->nat, the plan's position is
    fn(fn(nat)->nat,nat)->nat". Expected: compiles, [result = 2]. Actual:
    "no matching function for call to 'twice'". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.

Module IdAnyCastFlatFn.

Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition result : nat :=
  twice (id (fun (c : nat -> nat) (n : nat) => c n + 1)) (fun n : nat => n) 0.

End IdAnyCastFlatFn.

Crane Extraction "id_any_cast_flat_fn" IdAnyCastFlatFn.
