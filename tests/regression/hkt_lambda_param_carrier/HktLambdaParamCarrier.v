From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module HktLambdaParamCarrier.

(** In a generic function over a [Monad M], the class variable [M] leaks into
    the parameter type of an inner lambda instead of the method's own element
    type:

      return bind<_tcI0>(m, [=](const T2 &x) mutable {
        return bind<_tcI0>(f(x), [](M y) { return ret<_tcI0>(y); });
      });

    error: unknown type name 'M'   (should be T2) *)

Class Monad (M : Type -> Type) := {
  ret : forall A : Type, A -> M A ;
  bind : forall A B : Type, M A -> (A -> M B) -> M B
}.
Arguments ret {M _ A} _.
Arguments bind {M _ A B} _ _.

Instance OptM : Monad option := {
  ret := fun A x => Some x ;
  bind := fun A B m f => match m with None => None | Some x => f x end
}.

Definition twice {M} `{Monad M} {A} (m : M A) (f : A -> M A) : M A :=
  bind m (fun x => bind (f x) (fun y => ret y)).

Definition run (o : option nat) : option nat := twice o (fun n => Some (S n)).

End HktLambdaParamCarrier.

Crane Extraction "hkt_lambda_param_carrier" HktLambdaParamCarrier.run.
