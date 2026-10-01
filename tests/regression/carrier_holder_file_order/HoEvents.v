From ITree Require Import ITree.
Class Params : Type := { ptr : Type ; zero : ptr }.
Section WithParams.
  Context {Pa : Params}.
  Variant memE : Type -> Type := Load : ptr -> memE nat.
  Variant failE : Type -> Type := Fail : failE unit.
  Definition AllE := memE +' failE.
End WithParams.
