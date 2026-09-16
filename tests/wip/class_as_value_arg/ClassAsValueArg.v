(** Crane bug: a class used as an ordinary *value* argument type is emitted as
    the C++ concept of that class, in a position where a type is required.

    [Shw]'s method takes a [Params] as its first explicit argument -- the shape
    Vellvm gets from [Context {Pa : Params}] inside a section.  Crane lifts an
    explicit class argument of a plain [Definition] to a template type
    parameter, correctly; but for a class *method* it leaves it in the
    signature, where [Params] is a concept, not a type:

      static Nat shw(Params pa, memory_bit b) { return pa.width + b.tag; }

    and then passes the template parameter as a value at the call site.

    Expected: extracted C++ compiles.
    Actual:   error: expected 'auto' or 'decltype(auto)' after concept name
              error: 'pa' is not a class, namespace, or enumeration
              error: '_tcI0' does not refer to a value

    Seen in Vellvm 16 and 5 times respectively, on the methods of the [Show]
    and [RelDec] instances under [Context {Pa : Params}]. *)

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
