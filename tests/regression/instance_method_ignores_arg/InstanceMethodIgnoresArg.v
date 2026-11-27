From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.

(** An instance method that discards its argument ([fun _ => 1]) loses the
    argument on the way out: the method is emitted nullary while the concept
    still requires the one-argument shape, so the instance fails the concept's
    [static_assert] and its own body mentions the now-unbound template
    parameter [T1].  The same class with a method that actually matches on its
    argument comes out right, so this is the erasure of an unused parameter,
    not the class machinery. *)

Class C (A : Type) := { m : A -> nat }.

Inductive token := tok.

Global Instance ic : C token := { m := fun _ => 1 }.

Module InstanceMethodIgnoresArg.
  Definition run : nat := m tok.
End InstanceMethodIgnoresArg.

Crane Extraction "instance_method_ignores_arg" InstanceMethodIgnoresArg.
