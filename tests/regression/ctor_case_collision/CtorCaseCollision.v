From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module CtorCaseCollision.

(** Constructors are emitted as PascalCase nested structs, so two constructors
    of the same inductive that differ only in the case of their first letter
    compete for one C++ name.  Sibling reservation is done on that spelling, so
    the second one is renamed:

      using variant_t = std::variant<Foo, Foo0>; *)

Inductive c := Foo : nat -> c | foo : bool -> c.

Definition get (x : c) : nat := match x with Foo n => n | foo _ => 0 end.

End CtorCaseCollision.

Crane Extraction "ctor_case_collision" CtorCaseCollision.get.
