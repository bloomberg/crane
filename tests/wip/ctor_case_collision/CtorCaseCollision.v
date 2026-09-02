From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module CtorCaseCollision.

(** Two constructors of the same inductive that differ only in the case of
    their first letter both mangle to the C++ identifier [Foo]:

      using variant_t = std::variant<Foo, Foo>;

    error: redefinition of 'Foo'
    error: constructor cannot be redeclared *)

Inductive c := Foo : nat -> c | foo : bool -> c.

Definition get (x : c) : nat := match x with Foo n => n | foo _ => 0 end.

End CtorCaseCollision.

Crane Extraction "ctor_case_collision" CtorCaseCollision.get.
