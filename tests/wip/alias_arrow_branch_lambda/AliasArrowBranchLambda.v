(** Found by Ephyra round 24. A [match] whose branches are lambdas of type
    [list nat -> st nat], with [st A := nat -> A * nat] an arrow-valued
    alias, one branch binding a [let] first, passed as the initial value of
    a [fold_left]: the branches become an immediately invoked lambda whose
    declared return type unfolds the alias into the two-argument
    [crane::fn<std::pair<uint64_t, uint64_t>(List<uint64_t>, uint64_t)>],
    while each branch returns a one-argument lambda returning [st<uint64_t>]
    ("no viable conversion from returned value").  With an [if] and no
    [let], the branches are merged into one lambda and it compiles.
    Related to the arrow-alias defects of rounds 15 and 22
    ([local_fix_alias_function_result], [nested_fix_alias_result], fixed);
    this site still unfolds.

    Expected: compiles; [result = 10].
    Actual: "no viable conversion from returned value of type '(lambda ...)'
    to function return type 'crane::fn<std::pair<uint64_t, uint64_t>
    (List<uint64_t>, uint64_t)>'".  Under [CRANE_CHECK_IR] (the suite's
    setting) extraction stops first at "Crane IR check (typed fit)", a
    flat [fn(list nat, nat) -> nat * nat] put in the slot of the curried
    accumulator type. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.

Module AliasArrowBranchLambda.

Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).

Definition g (b : bool) : list nat -> st nat :=
  fold_left (fun (acc : list nat -> st nat) (_ : nat) => acc) []
    (match b with
     | true => (fun _ => sret 6)
     | false => let k := 4 in fun _ => sret k
     end).

Definition result : nat := fst (g true [] 0) + fst (g false [] 0).

End AliasArrowBranchLambda.

Crane Extraction "alias_arrow_branch_lambda" AliasArrowBranchLambda.
