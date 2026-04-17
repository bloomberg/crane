From Crane Require Extraction.

Module PolymorphicFunctionFieldProbe.

Record poly : Type := {
  apply : forall A : Type, A -> A
}.

Definition p : poly := {| apply := fun A x => x |}.

Definition sample_bool : bool := apply p bool true.

End PolymorphicFunctionFieldProbe.

Crane Extraction "polymorphic_function_field_probe" PolymorphicFunctionFieldProbe.
