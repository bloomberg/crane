From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** A typeclass instance at a function type (`Sz (nat -> nat)`): the instance
    method's parameter is concrete (`std::function<uint64_t(uint64_t)>`) even
    though the class abstracts over it, so calling it must not go through the
    erased `std::any` adapter. *)

Module InstanceAtFunctionType.
Class Sz (A : Type) := { sz : A -> nat }.
Instance SzN : Sz nat := { sz := fun n => n }.
Instance SzF : Sz (nat -> nat) := { sz := fun f => f 0 }.
Definition both {A B} `{Sz A} `{Sz B} (a : A) (b : B) : nat := sz a + sz b.
Definition go : nat := both 3 (fun n : nat => n + 4).
End InstanceAtFunctionType.
Crane Extraction "instance_at_function_type" InstanceAtFunctionType.
