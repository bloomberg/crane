(** Found by Ephyra round 28. Variant of round 25's
    [twice_composed_fn_destination] (fixed): the step of [twice], at
    [A := (nat -> nat) -> nat -> nat], is [hd_or d []] whose default [d] is a
    [let] of a two-argument local function [cf] and a lambda composing it,
    [fun c => cf (cg c)]. The typed-fit check finds the default, a flat
    two-argument function [fn(fn(nat)->nat, nat)->nat], put in the curried
    argument slot [fn(fn(nat)->nat)->fn(nat)->nat] (argument, regroup); the
    C++ compiles and is right. Expected: extracts under CRANE_CHECK_IR,
    [result = 11]. Actual: "Crane IR check (typed fit): ... (argument,
    regroup)". *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
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
