From Crane Require Import Mapping.Std.

(** The interface the bystander is passed through, in its own file: a module
    type inside the wrapper is the same defect in a worse position. *)
Module Type Ord.
  Parameter t : Set.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End Ord.
