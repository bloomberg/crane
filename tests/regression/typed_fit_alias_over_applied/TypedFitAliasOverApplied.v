(** Found by an Ephyra re-check of the round 24 typed-fit fixes, fixed.  A
    definition whose type is an alias of a function type ([st A := nat -> A
    * nat]) and whose body is a call returning that alias ([sret true]) is
    eta-expanded: the call is applied to the extra argument.  The call node
    recorded the callee's codomain, [st bool], as what the over-application
    yields, so the typed-fit check under [CRANE_CHECK_IR] put [st bool] in
    the slot of the eta-expansion's result, [bool * nat].  The C++ was right;
    extraction failed.  Fixed: [Calls.record_call_sig] reads what an
    over-application yields through the alias, past every argument both
    calls take, also where the inner call is kept as a constant ([f3]).

    Expected: extracts under [CRANE_CHECK_IR]; [run = true],
    [counter = 7]. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Module TypedFitAliasOverApplied.

Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).
Definition sbind {A B : Type} (m : st A) (f : A -> st B) : st B :=
  fun s => let (a, s') := m s in f a s'.
Definition sget : st nat := fun s => (s, s).

Definition f2 : st bool := sret true.
Definition f3 : st nat := sbind sget (fun n => sret (n + 2)).

Definition run : bool := fst (f2 5).
Definition counter : nat := fst (f3 5).

End TypedFitAliasOverApplied.

Crane Extraction "typed_fit_alias_over_applied" TypedFitAliasOverApplied.
