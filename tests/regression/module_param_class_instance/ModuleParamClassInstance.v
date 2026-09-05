From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module ModuleParamClassInstance.

(** A module-type [Parameter] whose type is a typeclass instance produces an
    ill-formed [requires] clause in the generated concept. *)
Class Weigh (A : Type) := { weigh : A -> nat }.

Module Type CARRIER.
  Parameter t : Type.
  Parameter inst : Weigh t.
  Parameter sample : t.
End CARRIER.

Module Doubler (C : CARRIER).
  #[local] Existing Instance C.inst.
  Definition twice (x : C.t) : nat := weigh x + weigh x.
  Definition on_sample : nat := twice C.sample.
End Doubler.

Module NatC <: CARRIER.
  Definition t := nat.
  #[export] Instance inst : Weigh nat := { weigh := fun n => n }.
  Definition sample : t := 5.
End NatC.

Module D := Doubler NatC.

Definition total : nat := D.on_sample + D.twice 7.

End ModuleParamClassInstance.
Crane Extraction "module_param_class_instance" ModuleParamClassInstance.
