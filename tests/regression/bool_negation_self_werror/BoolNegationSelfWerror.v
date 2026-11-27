From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    [orb b (negb b)] prints [(b || !(b))] and [andb b (negb b)] prints
    [(b && !(b))]; clang's -Wtautological-negation-compare rejects both under
    the suite's -Werror.  Same family as the folded self-comparisons
    (self_comparison_werror, self_comparison_mapped_werror). *)
Module BoolNegationSelfWerror.

Definition f (b : bool) : bool := orb b (negb b).
Definition g (b : bool) : bool := andb b (negb b).
(** The negation first. *)
Definition f' (b : bool) : bool := orb (negb b) b.
Definition g' (b : bool) : bool := andb (negb b) b.

End BoolNegationSelfWerror.

Crane Extraction "bool_negation_self_werror" BoolNegationSelfWerror.
