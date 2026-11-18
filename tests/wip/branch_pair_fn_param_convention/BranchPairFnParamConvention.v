From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List Strings.String.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Two [if] branches each build a pair holding a function on Rocq's [string]
    (no Std mapping): one lambda reads its argument (a match), the other
    ignores it.  After the callable-join fix both become [crane::fn], but one
    takes [const String &] and the other [String], so the conditional is
    ambiguous ("pair<fn<pt (const String &)>, ..> can be converted to
    pair<fn<pt (String)>, ..> and vice versa"). *)
Module BranchPairFnParamConvention.

Record pt : Type := mkpt { px : nat; py : bool }.

Definition t (b : bool) : nat :=
  px (fst (if b then ((fun y : String.string => match y with String.EmptyString => mkpt 1 true | String.String _ _ => mkpt 9 true end), 0)
           else ((fun _ : String.string => mkpt 2 true), 0)) String.EmptyString).

End BranchPairFnParamConvention.

Crane Extraction "branch_pair_fn_param_convention" BranchPairFnParamConvention.
