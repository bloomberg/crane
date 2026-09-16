(** A class used as an ordinary *value* argument type.

    [Shw]'s method takes a [Params] as its first explicit argument -- the shape
    Vellvm gets from [Context {Pa : Params}] inside a section.  A class is a
    concept in C++, so the instance meeting it is a type, not a value: the
    argument becomes one of the method's own template parameters, and every
    caller -- the concept's own probe included -- passes it as a template
    argument.

    Seen in Vellvm on the methods of the [Show] and [RelDec] instances under
    [Context {Pa : Params}]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class Params : Type := { width : nat }.

Record memory_bit : Set := mk_bit { tag : nat }.

Class Shw (T : Set) : Type := { shw : Params -> T -> nat }.

#[global] Instance Shw_memory_bit : Shw memory_bit :=
  {| shw pa b := width (Params := pa) + tag b |}.

Module ClassAsValueArg.

  Definition use (pa : Params) (b : memory_bit) : nat := shw pa b.

End ClassAsValueArg.

Crane Extraction "class_as_value_arg" ClassAsValueArg.
