From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Crane Require Import Mapping.Std.

(** A function of two or more arguments stored as a *value* is emitted
    uncurried, [function<Nat (Nat, Nat)>], while every slot that holds a
    function value expects the curried spelling
    [function<function<Nat (Nat)> (Nat)>].  The two never meet: "no viable
    conversion".  One-argument function values are fine, so this is the
    currying convention for stored functions, not function storage itself. *)

Module MultiArgFunctionValue.
  Definition o : option (nat -> nat -> nat) := Some Nat.add.

  Definition partial : option (nat -> nat) :=
    match o with None => None | Some f => Some (f 1) end.

  Definition run : nat := match partial with None => 0 | Some g => g 2 end.
End MultiArgFunctionValue.

Crane Extraction "multi_arg_function_value" MultiArgFunctionValue.
