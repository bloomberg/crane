From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    In a module instantiating a module type with [t := bool], [op] applies the class method [mop] to two lets (one binding an unused [inr]): under CRANE_CHECK_IR=1 "coercion position: a coercion in M3_2.op is lowered against none, the plan's position is M3_2.t". *)
Module InstanceOpCoercionPosition.
CoInductive stream : Type := SCons : nat -> stream -> stream.
Class Mon (A : Type) := { munit : A; mop : A -> A -> A }.
#[global] Instance mon_bool : Mon bool := { munit := false; mop := orb }.

Module Type SIG3.
  Parameter t : Type.
  Parameter d : t.
End SIG3.

Module F3 (E : SIG3).
End F3.
Module M3_1 <: SIG3.
  Definition t : Type := (list nat).
  Definition d : t := [4%nat; 11%nat; 8%nat; 4%nat].
End M3_1.
Module M3_2 <: SIG3.
  Definition t : Type := bool.
  Definition d : t := true.
  Definition op (u18 v19 : t) : t := (mop (let x20 := u18 in x20) (let x21 := (@inr bool nat 9%nat) in v19)).
End M3_2.
End InstanceOpCoercionPosition.

Crane Extraction "instance_op_coercion_position" InstanceOpCoercionPosition.
