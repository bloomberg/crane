(** Found by Ephyra round 29 (reported by the round-28 fixer). Variant of
    round 28's [id_any_cast_flat_fn]. [Datatypes.id] is typed by the alias
    [ID := forall A, A -> A], so its argument and result are erased to
    [crane::obj]. Applied directly to a function and then over-applied, the
    result is cast back to the boxed-whole [crane::fn<crane::obj(crane::obj)>]
    and called with the remaining arguments, each boxed. Fixed: those
    arguments were boxed raw, by a converting construction that ignored
    their type, so a lambda literal was put in the box as itself
    ([crane::obj([](uint64_t n) { ... })]) while the [crane_erase_fn]
    adapter around the function reads its boxed argument as a callable, and
    the cast inside the adapter threw [std::bad_any_cast]. Each argument of
    an erased callee is now boxed through [Coerce.decide]: a callable is
    boxed whole ([crane_erase_fn]), the way a recovery reads it back.
    Expected and now: [one_arg 4 = 5], [two_args 4 = 5], [control 4 = 5]. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.

Module IdOverAppliedLambdaArg.

Definition one_arg (k : nat) : nat :=
  id (fun (c : nat -> nat) => c k) (fun n => n + 1).

Definition two_args (k : nat) : nat :=
  id (fun (c : nat -> nat) (n : nat) => c n + 1) (fun n => n) k.

Definition control (k : nat) : nat :=
  let f := fun n => n + 1 in id (fun (c : nat -> nat) => c k) f.

End IdOverAppliedLambdaArg.

Crane Extraction "id_over_applied_lambda_arg" IdOverAppliedLambdaArg.
