(** A typeclass over a type constructor ([M : Type -> Type]).  The instance
    method's body erases the carrier's argument to [std::any] while the value
    it is applied to keeps its concrete type, so the two disagree:

    {v
      std::holds_alternative<Option<std::any>::Some, Option<Nat>::Some,
                             Option<Nat>::None>
      static assertion failed ... type not found in type list
    v} *)

Require Crane.Extraction.

Module HktInstanceAnyMismatch.

Class Mon (M : Type -> Type) :=
  { ret : forall A, A -> M A
  ; bind : forall A B, M A -> (A -> M B) -> M B }.

Instance optMon : Mon option :=
  {| ret := fun A a => Some a
   ; bind := fun A B m f => match m with Some a => f a | None => None end |}.

Definition test : option nat :=
  @bind option optMon nat nat (@ret option optMon nat 1)
        (fun n => @ret option optMon nat (S n)).

End HktInstanceAnyMismatch.

Crane Extraction "hkt_instance_any_mismatch" HktInstanceAnyMismatch.
