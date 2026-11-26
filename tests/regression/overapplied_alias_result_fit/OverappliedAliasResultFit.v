(** Found by Ephyra round 28. A constant of a function-type alias
    ([st A := nat -> A * nat]) defined by an over-applied polymorphic call,
    [hd_or (fun _ => sret 7) [] 3], at [A := nat -> st nat]. The typed-fit
    check found the call's [st nat] result put in a slot of type
    [nat * nat] (destination, unrelated). The C++ compiled and was right.

    Fixed: the constant is eta-expanded, so the call kept as a constant is
    applied to [3] and then to the added argument; the over-application's
    type dropped the callee's declared arrows and the outer call's
    arguments, but not those of the call in between, and so stopped one
    arrow short ([Calls.record_call_sig] counts every call of the call).

    Expected: extracts under CRANE_CHECK_IR, [result = 705]. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module OverappliedAliasResultFit.

Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).
Definition hd_or {A : Type} (d : A) (l : list A) : A := match l with [] => d | x :: _ => x end.
Definition f : st nat := hd_or (fun _ : nat => sret 7) (@nil (nat -> st nat)) 3.
Definition result : nat := let (a, s) := f 5 in a * 100 + s.

End OverappliedAliasResultFit.

Crane Extraction "overapplied_alias_result_fit" OverappliedAliasResultFit.
