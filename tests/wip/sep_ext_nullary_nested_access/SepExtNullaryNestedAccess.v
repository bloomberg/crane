(** Regression: accessing a nullary field through a nested sub-module
    path inside a functor must emit () in C++.
    Pattern: O.I.val where O is a functor parameter whose module type
    declares a sub-module I with a nullary field val.
    Crane currently emits O::I::val (function reference) instead of
    O::I::val() (function call), causing errors like:
      cannot initialize a variable of type 'T' with an lvalue of type 'const T &()' *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.

Module Type Inner.
  Parameter val : nat.
End Inner.

Module Type Outer.
  Declare Module I : Inner.
  Parameter name : nat.
End Outer.

Module Worker (O : Outer).

  Definition get_inner_val : nat := O.I.val.

  Definition get_name : nat := O.name.

  Definition sum : nat := Nat.add O.I.val O.name.

End Worker.

Crane Separate Extraction Worker.
