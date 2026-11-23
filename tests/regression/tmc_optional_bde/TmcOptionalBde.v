(** Found by Ephyra (round 21, BDE flavour). [List.app] ([++]) under
    [Mapping.BDE], built as BDE tests are ([scripts/compile-bde.sh]).

    Expected: compiles; [total = 6].

    Fixed: [app] is lowered modulo cons (TMC) and builds the result front to
    back from a [bsl::optional<List<A>> _root]; the demand for [optional]
    was raised, but a BDE header included only a fixed list of standard
    headers, so [<bsl_optional.h>] was never included ("no template named
    'optional' in namespace 'bsl'").  A BDE header now includes every
    standard header demanded, as [bsl_<h>.h] for what Crane writes in
    [bsl::]. *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Module TmcOptionalBde.
Definition joined : list nat := [1; 2] ++ [3].
Definition total : nat := fold_left Nat.add joined 0.
End TmcOptionalBde.
Crane Extraction "tmc_optional_bde" TmcOptionalBde.
