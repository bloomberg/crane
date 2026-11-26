(** Found by Ephyra round 28. A top-level constant of a function-type alias
    ([st A := nat -> A * nat]) defined by a local fixpoint over [st nat],
    applied to [[]]: its accumulator is an [st nat] and both branches return
    [sret _]. Under CRANE_CHECK_IR the typed-lowering check finds an
    application lowered with no type ("a apply lowered without a type, in
    f: apply/1:apply/2:fixpoint"). The C++ compiles and is right. Kin of
    round 15's [local_fix_alias_function_result] and round 25's
    [local_fix_alias_acc_join] (both fixed), which failed the typed-fit
    check. Expected: extracts under CRANE_CHECK_IR, [result = 703]. Actual:
    "Crane IR check (typed lowering): a apply lowered without a type". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
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
