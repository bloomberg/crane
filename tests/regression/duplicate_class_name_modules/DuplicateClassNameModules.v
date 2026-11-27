From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.

(** Two modules each declare a class called [C].  A class is emitted as a
    concept at file scope rather than inside its module's struct, so the second
    one is a redefinition of the first. *)

Module M1.
  Class C (A : Type) := { m : A -> nat }.
  Global Instance i : C nat := { m := fun x => x }.
End M1.

Module M2.
  Class C (A : Type) := { m : A -> nat }.
  Global Instance i : C bool := { m := fun b => if b then 1 else 0 }.
End M2.

Module DuplicateClassNameModules.
  Definition run : nat := M1.m 1 + M2.m true.
End DuplicateClassNameModules.

Crane Extraction "duplicate_class_name_modules" DuplicateClassNameModules.
