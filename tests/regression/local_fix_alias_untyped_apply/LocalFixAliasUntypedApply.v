(** Found by Ephyra round 28. A top-level constant of a function-type alias
    ([st A := nat -> A * nat]) defined by a local fixpoint over [st nat],
    applied to [[]]: its accumulator is an [st nat] and both branches return
    [sret _]. Under CRANE_CHECK_IR the typed-lowering check found an
    application lowered with no type ("a apply lowered without a type, in
    f: apply/1:apply/2:fixpoint"). The C++ compiled and was right. Kin of
    round 15's [local_fix_alias_function_result] and round 25's
    [local_fix_alias_acc_join].

    Fixed: the constant is eta-expanded, so the fixpoint's application is
    applied once more; its Core type was read by dropping arrows from the
    fixpoint's, which ran out at the alias [st nat].  The arrows are now
    dropped through a function alias ([Type_util.strip_arrows_through_aliases],
    read by [Typed_checks.core_type_of] and [Calls.record_call_sig]), so
    the application is a [nat * nat].

    Expected: extracts under CRANE_CHECK_IR, [result = 703]. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module LocalFixAliasUntypedApply.

Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).
Definition f : st nat :=
  let fix go (l : list bool) (acc : st nat) {struct l} : st nat :=
    match l with [] => sret 7 | _ :: r => go r (sret 8) end in
  go [] (sret 9).
Definition result : nat := let (a, s) := f 3 in a * 100 + s.

End LocalFixAliasUntypedApply.

Crane Extraction "local_fix_alias_untyped_apply" LocalFixAliasUntypedApply.
