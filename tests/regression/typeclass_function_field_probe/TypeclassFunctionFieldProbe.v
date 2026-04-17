From Crane Require Extraction.

Module TypeclassFunctionFieldProbe.

Class HasEndo (A : Type) := {
  endo : A -> A
}.

#[global] Instance boolEndo : HasEndo bool := {
  endo := negb
}.

Definition use {A : Type} `{HasEndo A} (x : A) : A :=
  endo (endo x).

Definition sample : bool := use true.

End TypeclassFunctionFieldProbe.

Crane Extraction "typeclass_function_field_probe" TypeclassFunctionFieldProbe.
