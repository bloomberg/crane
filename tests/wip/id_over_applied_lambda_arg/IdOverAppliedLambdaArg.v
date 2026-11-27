(** Found by Ephyra round 29 (reported by the round-28 fixer). Variant of
    round 28's [id_any_cast_flat_fn] (regression). [Datatypes.id] is typed
    by the alias [ID := forall A, A -> A], so its argument and result are
    erased to [crane::obj]. Applied directly to a function and then
    over-applied, the result is cast back to the boxed-whole
    [crane::fn<crane::obj(crane::obj)>] and called with the remaining
    arguments, each boxed. A lambda literal among those arguments is put in
    the box raw ([crane::obj([](uint64_t n) { ... })]), while the
    [crane_erase_fn] adapter around the function reads its boxed argument
    as a callable, so the cast inside the adapter throws. The same call
    with the lambda bound by a [let] first ([control]) works, as does a
    user-defined polymorphic identity, and [id] over-applied to a non-function
    argument. Expected: [one_arg 4 = 5], [two_args 4 = 5], [control 4 = 5].
    Actual: compiles, then "uncaught exception of type std::bad_any_cast"
    at the first call. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Module IdOverAppliedLambdaArg.

Definition one_arg (k : nat) : nat :=
  id (fun (c : nat -> nat) => c k) (fun n => n + 1).

Definition two_args (k : nat) : nat :=
  id (fun (c : nat -> nat) (n : nat) => c n + 1) (fun n => n) k.

Definition control (k : nat) : nat :=
  let f := fun n => n + 1 in id (fun (c : nat -> nat) => c k) f.

End IdOverAppliedLambdaArg.

Crane Extraction "id_over_applied_lambda_arg" IdOverAppliedLambdaArg.
