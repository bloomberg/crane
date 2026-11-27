(** Found by Ephyra round 28. Variant of round 25's
    [twice_composed_fn_destination]: the step of [twice], at
    [A := (nat -> nat) -> nat -> nat], is [hd_or d []] whose default [d] is a
    [let] of a two-argument local function [cf] and a lambda composing it,
    [fun c => cf (cg c)]. The [let] was lowered as an immediately invoked
    lambda returning the curried closure its slot asks for, but typed at its
    Core type's flat spelling [fn(fn(nat)->nat, nat)->nat], so the typed-fit
    check refused it in the curried argument slot (argument, regroup); the
    C++ compiled and was right.

    Fixed: an undeclared immediately invoked lambda is typed as what its
    returns are where they agree ([Match_types.value_iife_typed]). *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module ComposedFnDefaultRegroup.

Definition hd_or {A : Type} (d : A) (l : list A) : A := match l with [] => d | x :: _ => x end.
Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition result : nat :=
  twice (hd_or (let cf := fun (b : bool) (n : nat) => if b then n + 1 else n + 5 in
                let cg := fun g : nat -> nat => Nat.eqb (g 0) 0 in
                fun c : nat -> nat => cf (cg c))
               (@nil ((nat -> nat) -> nat -> nat)))
    (fun n : nat => n) 6.

End ComposedFnDefaultRegroup.

Crane Extraction "composed_fn_default_regroup" ComposedFnDefaultRegroup.
