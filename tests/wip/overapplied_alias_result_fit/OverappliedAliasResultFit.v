(** Found by Ephyra round 28. A constant of a function-type alias
    ([st A := nat -> A * nat]) defined by an over-applied polymorphic call,
    [hd_or (fun _ => sret 7) [] 3], at [A := nat -> st nat]. The typed-fit
    check finds the call's [st nat] result put in a slot of type
    [nat * nat] (destination, unrelated): the destination is read through
    the alias one arrow further than the value. The C++ compiles and is
    right. Kin of round 25's [fn_list_state_alias_fit] (fixed). Expected:
    extracts under CRANE_CHECK_IR, [result = 705]. Actual: "Crane IR check
    (typed fit): a value of type st<nat> put in a slot of type prod<nat,nat>
    (destination, unrelated)". *)
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
