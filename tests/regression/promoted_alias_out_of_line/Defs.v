(** A type-class field erased to [crane::obj] is written as a file-scope
    alias of the same name, [using iptr = crane::obj;], and an inductive
    declared over the class takes it as its parameter: [Dval<iptr>].

    [F.v] is written as the struct [F] (its [size] collides with
    [Other.v]'s), and its polymorphic [lst] is defined out of line in the
    header, after the struct, as [F::lst].  Its parameter type names [iptr],
    which [F] does not declare: the type printer writes a promoted name in an
    out-of-line definition qualified by the struct it is a member of, except
    a name the header declares at file scope, which it leaves bare.  This is
    the test that reaches that exception: [F::iptr] would not compile. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class IPtr := { iptr : Type ; zero_iptr : iptr }.

Section withIPtr.
  Context {IP : IPtr}.
  Inductive dval : Type := | DPtr : iptr -> dval | DNat : nat -> dval.
End withIPtr.

#[global] Instance natIPtr : IPtr := {| iptr := nat ; zero_iptr := 0 |}.
