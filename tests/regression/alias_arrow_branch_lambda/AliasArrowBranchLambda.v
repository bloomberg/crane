(** Found by Ephyra round 24. A [match] whose branches are lambdas of type
    [list nat -> st nat], with [st A := nat -> A * nat] an arrow-valued
    alias, one branch binding a [let] first, passed as the initial value of
    a [fold_left]: the branches became an immediately invoked lambda whose
    declared return type unfolded the alias into the two-argument
    [crane::fn<std::pair<uint64_t, uint64_t>(List<uint64_t>, uint64_t)>],
    while each branch returns a one-argument lambda returning [st<uint64_t>]
    ("no viable conversion from returned value"; under [CRANE_CHECK_IR],
    "Crane IR check (typed fit)" first).  Related to the arrow-alias
    defects of rounds 15 and 22 ([local_fix_alias_function_result],
    [nested_fix_alias_result]).

    Fixed: the join declares the lambda at its slot's function type where
    that is the annotation's grouped otherwise, and compared the two
    without unfolding aliases, so [crane::fn<st<uint64_t>(List<uint64_t>)>]
    did not count as [list nat -> nat -> nat * nat] ([Match_types.declared_at]
    now compares them with the unit's aliases unfolded).

    Expected: compiles; [result = 10]. *)
From Crane Require Import Mapping.NatInt.
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
