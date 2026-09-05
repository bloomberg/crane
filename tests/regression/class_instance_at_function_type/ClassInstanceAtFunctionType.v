From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module ClassInstanceAtFunctionType.

(** A typeclass instance at a function type splices the member's own
    parameters into the emitted method, so the arity no longer matches the
    concept. *)
Class Weigh (A : Type) := { weigh : A -> nat }.

Instance WeighNat : Weigh nat := { weigh := fun n => n }.
Instance WeighFn : Weigh (nat -> nat) := { weigh := fun f => f 10 }.
Instance WeighPair (A B : Type) `{Weigh A} `{Weigh B} : Weigh (A * B) :=
  { weigh := fun p => weigh (fst p) + weigh (snd p) }.

Definition total : nat :=
  weigh 1 + weigh (fun n : nat => n * 2) + weigh (3, fun n : nat => n + 1).

End ClassInstanceAtFunctionType.
Crane Extraction "class_instance_at_function_type" ClassInstanceAtFunctionType.
