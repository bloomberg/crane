From Stdlib Require Import List.
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module HktInstanceCarrierSlot.

(** An instance method that delegates to a standalone polymorphic function
    passes the *carrier* [F A] where the callee's *element* type belongs:

      template <typename _A0> static Nat sz(List<_A0> a0) {
        return llen<List<std::any>>(a0);      // should be llen<_A0>
      }

    error: no matching conversion for functional-style cast from 'const Nat'
           to 'List<std::any>' *)

Class Sizeable (F : Type -> Type) := { sz : forall A : Type, F A -> nat }.
Arguments sz {F _ A} _.

Fixpoint llen {A} (l : list A) : nat :=
  match l with nil => 0 | cons _ r => S (llen r) end.

Instance SL : Sizeable list := { sz := fun A l => llen l }.

Definition run (l : list nat) : nat := sz l.

End HktInstanceCarrierSlot.

Crane Extraction "hkt_instance_carrier_slot" HktInstanceCarrierSlot.run.
