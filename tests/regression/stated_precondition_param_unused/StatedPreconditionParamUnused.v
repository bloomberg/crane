From Crane Require Import Extraction.

Module StatedPreconditionParamUnused.

(** C++ cannot check [m <= n] of a [nat] witness, so the precondition is
    stated in a comment that spells [n], written [_x]: the body never reads
    it.  A comment reads nothing, so [n] stays unnamed, or
    [-Werror,-Wunused-parameter] rejects the function. *)
Definition get (n : nat) (b : { m : nat | m <= n }) : nat := proj1_sig b.

Definition result : nat := get 5 (exist _ 3 (le_S _ _ (le_S _ _ (le_n 3)))).

End StatedPreconditionParamUnused.

Crane Extraction "stated_precondition_param_unused" StatedPreconditionParamUnused.
