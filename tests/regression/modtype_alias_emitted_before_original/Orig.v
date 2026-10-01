From Crane Require Import Mapping.Std.

(** The original.  [tag] is here so the file has a term-level declaration, and
    so is reached for a reason other than the module type -- which is what puts
    this file's entry in the dependency graph at all, and is half of what
    inverted the order. *)

Module Type DecOrig.
  Parameter t : Set.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End DecOrig.

Definition tag : nat := 7.
