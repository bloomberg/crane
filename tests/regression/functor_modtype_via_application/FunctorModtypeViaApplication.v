From Crane Require Import Mapping.Std.
From Crane Require Extraction.

(** A module type declared in a functor's body, reached through an
    application of the functor: [G.S] is the functor's concept [F_S] over
    the application's argument, not a member of [G]. *)
Module FunctorModtypeViaApplication.

Module Type Base.
  Parameter t : Type.
End Base.

Module F (X : Base).
  Module Type S.
    Parameter u : Type.
    Parameter f : u -> X.t.
  End S.
  Module Use (Y : S).
    Definition g (y : Y.u) : X.t := Y.f y.
  End Use.
End F.

Module NatB <: Base.
  Definition t := nat.
End NatB.

Module G := F NatB.

Module YY <: G.S.
  Definition u := bool.
  Definition f (b : bool) : nat := if b then 1 else 0.
End YY.

Module H := G.Use YY.

Module K (Z : G.S).
  Definition h (z : Z.u) : nat := Z.f z.
End K.

Module KK := K YY.

Definition res : bool := Nat.eqb (H.g true + KK.h false) 1.

End FunctorModtypeViaApplication.

Crane Extraction "functor_modtype_via_application" FunctorModtypeViaApplication.
