(** Found by Ephyra (round 21, BDE flavour). [List.app] ([++]) under
    [Mapping.BDE], built as BDE tests are ([scripts/compile-bde.sh]).

    Expected: compiles; [total = 6].

    Actual: compile error "no template named 'optional' in namespace 'bsl';
    did you mean 'std::optional'?". [app] is lowered modulo cons (TMC): it
    builds the result front to back from a [bsl::optional<List<A>> _root],
    but the header never includes [<bsl_optional.h>]. Also on main (where a
    second error follows: no matching [crane_raw]). *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Module TmcOptionalBde.
Definition joined : list nat := [1; 2] ++ [3].
Definition total : nat := fold_left Nat.add joined 0.
End TmcOptionalBde.
Crane Extraction "tmc_optional_bde" TmcOptionalBde.
