From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** WIP: A typeclass instance at a function type (`Sz (nat -> nat)`) inserts an
    `any_cast<std::function<std::any(std::any)>>` on a parameter whose C++ type
    is already the concrete `std::function<uint64_t(uint64_t)>`. *)

Module InstanceAtFunctionType.
Class Sz (A : Type) := { sz : A -> nat }.
Instance SzN : Sz nat := { sz := fun n => n }.
Instance SzF : Sz (nat -> nat) := { sz := fun f => f 0 }.
Definition both {A B} `{Sz A} `{Sz B} (a : A) (b : B) : nat := sz a + sz b.
Definition go : nat := both 3 (fun n : nat => n + 4).
End InstanceAtFunctionType.
Crane Extraction "instance_at_function_type" InstanceAtFunctionType.
