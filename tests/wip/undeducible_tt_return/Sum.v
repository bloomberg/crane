From Crane Require Extraction.

Variant sum1 (E F : Type -> Type) (X : Type) : Type :=
  | inl1 (e : E X)
  | inr1 (f : F X).
Arguments inl1 {E F X}.
Arguments inr1 {E F X}.

Definition swap {E F : Type -> Type} {X : Type} (ab : sum1 E F X) : sum1 F E X :=
  match ab with inl1 e => inr1 e | inr1 b => inl1 b end.
