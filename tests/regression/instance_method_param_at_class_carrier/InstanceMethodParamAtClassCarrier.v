(* An instance method's parameter is erased to [std::any] when the instance is
   at another class's carrier rather than at a concrete type.

     static Nat show(std::any a0) { return _tcI0::render(a0); }

   giving `no viable conversion from 'std::any' to 'Nat'` -- Vellvm's h:12309,
   the [showIptr] site, where the same parameter should be [Z].

   The correct spelling is declared one line above the erased one and goes
   unused: the instance's own [using carr = typename _tcI0::carr;], which is
   Vellvm's unused [using iptr] at h:12310.  So the type is in hand at the
   declaration; it is the parameter that does not take it.

   The variable is the instance's type argument, not eta.  A control that
   varies eta alone -- writing [show := fun (x : carr) => render x] for
   [show := render] -- erases identically, so the distance between the
   projection and the method is not what decides.  A control at a concrete
   type ([Instance showNat : Show nat]) emits [static Nat show(Nat n)] and
   compiles.

   Watch the emitted text, not the error count: widening what the parameter
   position accepts would compile while leaving the erasure in place. *)

From Crane Require Import Extraction.

Class Carrier := { carr : Type ; render : carr -> nat }.
Class Show (A : Type) := { show : A -> nat }.

(* The value's type is named nowhere in the instance body, only in [Carrier]. *)
#[global] Instance showCarr {C : Carrier} : Show carr := {| show := render |}.

(* A generic consumer, as Vellvm's [show_dvalue_base] is: the instance is used
   at the class's carrier, not at a concrete type. *)
Definition describe {C : Carrier} (x : carr) : nat := show x.

#[global] Instance natCarrier : Carrier := {| carr := nat ; render := fun n => n |}.

Module InstanceMethodParamAtClassCarrier.
  Definition run : nat := @describe natCarrier 7.
End InstanceMethodParamAtClassCarrier.

Crane Extraction "instance_method_param_at_class_carrier"
  InstanceMethodParamAtClassCarrier.
