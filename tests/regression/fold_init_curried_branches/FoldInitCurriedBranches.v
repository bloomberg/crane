(** Found by Ephyra (round 19). A [fold_left] whose accumulator is a
    two-argument function ([nat -> bool -> Z]), with a [match] as its
    initial value whose branches return two-argument lambdas. Akin to the
    fixed [fold_curried_accumulator], in the initial value's position.

    Fixed: the match, bound ahead as an immediately invoked lambda, was
    declared to return the flat [crane::fn<int64_t(uint64_t, bool)>] its
    Core annotation spells, while its branches were written under the
    return type in force, the fold's curried accumulator type
    [crane::fn<crane::fn<int64_t(bool)>(uint64_t)>], and returned curried
    lambdas ("no viable conversion from returned value"). A match invoked
    in place now joins its callables at the type its branches are written
    under where that regroups the annotation's arrows
    ([Match_types.joined_at]). Expected [t_1 = 12]. *)
From Crane Require Import Mapping.NatInt Mapping.ZInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith.
Import ListNotations.
Module FoldInitCurriedBranches.
Definition pick (n : nat) : nat :=
  (fun w : nat -> bool -> Z => Z.to_nat (w 0 true))
    (fold_left (fun (acc : nat -> bool -> Z) (_ : nat) => fun _ _ => 0%Z) []
       (match n with
        | O => fun (_ : nat) (_ : bool) => 5%Z
        | S _ => fold_left (fun (acc : nat -> bool -> Z) (_ : bool) => acc) [] (fun (_ : nat) (_ : bool) => 7%Z)
        end)).
Definition t_1 : nat := pick 0 + pick 1.
End FoldInitCurriedBranches.
Crane Extraction "fold_init_curried_branches" FoldInitCurriedBranches.
