(** A constructor field takes its name from the Rocq binder.  When that name is
    also the name of a type in scope at the field's declaration — here the
    enclosing inductive [t] itself — the member declaration hides the type, and
    every later use of the bare type name in the same struct stops naming a
    type.  The field's name has to be renamed away from the types visible
    beside it. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.

Module CtorFieldShadowsType.
  Inductive t : Set := Mk (t : nat) (extra : nat).

  Definition total (x : t) : nat := match x with Mk a b => a + b end.

  Definition answer : nat := total (Mk 1 2).
End CtorFieldShadowsType.

Crane Extraction "ctor_field_shadows_type" CtorFieldShadowsType.
