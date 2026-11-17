From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_functor_modtype_via_application.Inner.

(** A module type declared in the body of a functor of another file, reached
    through an application of the functor, as a functor parameter's type and
    as the base of a module type: [G.S] is that file's concept [F_S] over the
    application's argument. *)
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

Module Type S2 := G.S.

Module K2 (Z : S2).
  Definition h2 (z : Z.u) : nat := Z.f z.
End K2.

Module KK2 := K2 YY.

Definition res : bool := Nat.eqb (H.g true + KK.h false + KK2.h2 true) 2.

Crane Separate Extraction res.
