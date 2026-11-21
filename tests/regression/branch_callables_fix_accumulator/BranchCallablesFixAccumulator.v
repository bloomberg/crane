(** Found by Ephyra (round 19). A variant left by the callable-join fixes of
    [branch_callables_distinct_types] and [branch_callables_curried_join]:
    a match whose branches return a composed let-lambda ([fun c => cf (cg
    c)]) and a plain lambda, passed as the accumulator argument of a local
    fixpoint, inside an argument of a beta-redex.

    Fixed: the match takes a record apart before its [if], and that
    destructuring was an immediately invoked lambda built with no return
    type, the one such lambda the callable join (a lambda returning from
    several places, one a callable, is declared at a [crane::fn]) did not
    reach: its branches returned two distinct closure types ("return type
    '(lambda at ...)' must match previous return type"). Every immediately
    invoked lambda computing a value now goes through one join
    ([Match_types.value_iife]). Expected [t_1 = 0]. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module BranchCallablesFixAccumulator.

Record r3 : Type := mkr3 { ra : nat; rb : list nat; rc : bool }.

Definition pick (b : bool) : nat :=
  (fun w : (nat -> nat) -> list nat => List.length (w (fun s : nat => s)))
    (let fix go (l : list nat) (acc : (nat -> nat) -> list nat) {struct l}
           : (nat -> nat) -> list nat :=
       match l with
       | [] => fun _ : nat -> nat => []
       | _ :: r => go r (fun _ : nat -> nat => [])
       end in
     go []
       (match fold_left (fun (a : r3) (_ : r3) => mkr3 0 [] true) [] (mkr3 0 [] b) with
        | mkr3 _ _ c0 =>
          if c0 then
            let cf := fun _ : bool => [1; 2] in
            let cg := fun _ : nat -> nat => true in
            fun c : nat -> nat => cf (cg c)
          else fun _ : nat -> nat => [3]
        end)).

Definition t_1 : nat := pick true + pick false.

End BranchCallablesFixAccumulator.

Crane Extraction "branch_callables_fix_accumulator" BranchCallablesFixAccumulator.
