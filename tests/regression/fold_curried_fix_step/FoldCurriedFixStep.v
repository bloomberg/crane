(** Found by Ephyra (round 22). A [fold_right] over a two-argument
    function accumulator ([nat -> nat -> nat]) whose step defines a local
    fixpoint taking such a function as its own accumulator. Akin to the
    fixed [fold_curried_accumulator] (round 1) and
    [fold_init_curried_branches] (round 19), inside the step.

    Expected: compiles; [result = 34] (the fixpoint returns the
    accumulator unchanged, so it is [base 3 4]).

    Fixed: compile error "no matching function for call to object of type
    'const (lambda ...)'": the fold's accumulator is the curried
    [crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>], but the local
    fixpoint's accumulator parameter is the flat [crane::fn<uint64_t(uint64_t,
    uint64_t)>], so [go(nil, acc, _pa0, _pa1)] did not type, and the
    partial application's closure took both arguments at once where the
    fold takes them one at a time.  Two rules now hold wherever a function
    value crosses between the two spellings: a variable holding a function
    curried, read where its arguments are taken at once, is read through an
    adapter that applies it group by group (the converse of the curried
    adapter a flat one already got), and the closure a partial application
    builds groups its parameters as the position it fills does. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Module FoldCurriedFixStep.
Definition g (base : nat -> nat -> nat) (l : list nat) : nat -> nat -> nat :=
  fold_right (fun (e : nat) (acc : nat -> nat -> nat) =>
                let fix go (m : list bool) (a : nat -> nat -> nat) {struct m} : nat -> nat -> nat :=
                  match m with [] => acc | _ :: r => go r (fun x y => x + y + e) end in
                go [] acc) base l.
Definition result : nat := g (fun x y => x * 10 + y) [1; 2] 3 4.
End FoldCurriedFixStep.
Crane Extraction "fold_curried_fix_step" FoldCurriedFixStep.
