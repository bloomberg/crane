(* A bare constructor passed to [fmap] is eta-expanded into a lambda whose
   parameter extraction never gave a type, so it is written [std::any] while
   the body it wraps is at the concrete type -- and the error lands inside the
   lambda, at the constructor call:

     error: no viable conversion from 'std::any' to 'Dv'

   Expected: the parameter is spelled at the type the call already pins, which
   is sitting two tokens away in [fmap]'s own explicit template arguments --
   the second of them is the source index:

     Functor0::template fmap<Functor_Monad<_tcI0>, Dv, Sum<Exc, Dv>>(
         [](Dv x) { return Sum<Exc, Dv>::inr(x); }, std::move(m))

   The eta-expansion is Crane's, not the source's: writing the lambda out by
   hand in Rocq ([fmap (fun x => inr x) m]) gives the binder a type and comes
   out correct. It is the point-free [inr] that has nothing to go on.

   This is the inverse of handler_lambda_targ_undeclared, where the lambda's
   *return* was erased and the consumer could not convert it back.

   Reduced from Vellvm, where it was the largest remaining cluster: eight
   copies of ExtLib's [inr <$> e], five at [Dvalue_base]
   (IntrinsicsDefinitions.v:541 and neighbours) and three at [Dvalue]
   (Libraries.v:75, Denotation.v:936). *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads Structures.Functor.

Inductive Exc : Set := Oops.
Inductive Dv : Set := DV (n : nat).

#[global] Instance Functor_Monad (M : Type -> Type) `{Monad M} : Functor M :=
  { fmap := fun A B f x => bind x (fun a => ret (f a)) }.

#[global] Instance Monad_option : Monad option :=
  { ret := fun _ x => Some x;
    bind := fun _ _ m f => match m with Some x => f x | None => None end }.

Definition raise_right {M} `{Monad M} (m : M Dv) : M (sum Exc Dv) :=
  fmap (@inr Exc Dv) m.

Module FmapErasedLambdaParam.
  Definition go (n : nat) : option (sum Exc Dv) :=
    raise_right (Some (DV n)).
End FmapErasedLambdaParam.

Crane Extraction "fmap_erased_lambda_param" FmapErasedLambdaParam.
