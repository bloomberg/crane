From Crane Require Extraction.
From CraneTestsWIP Require undeducible_tt_return.Sum.

Notation "E ~> F" := (forall X : Type, E X -> F X) (at level 99) : type_scope.

(* ITree's [case_]: the result is itself a natural transformation, so the
   scrutinee arrives through a lambda rather than a named parameter, and its
   type index [X] is universally quantified (hence erased). *)
Definition case_ {E F M : Type -> Type} (f : E ~> M) (g : F ~> M)
  : (fun X => Sum.sum1 E F X) ~> M :=
  fun _ ab => match ab with Sum.inl1 e => f _ e | Sum.inr1 b => g _ b end.
