From Crane Require Extraction.

Module TypeclassMethodFunctionReturnProbe.

Class Factory (A : Type) := {
  make : A -> A -> A
}.

#[global] Instance boolFactory : Factory bool := {
  make x y := if x then y else x
}.

Definition partial : bool -> bool := make true.

Definition sample : bool := partial false.

End TypeclassMethodFunctionReturnProbe.

Crane Extraction "typeclass_method_function_return_probe" TypeclassMethodFunctionReturnProbe.
