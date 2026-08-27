From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** A parameterised inductive with a function field
    (`endo A := E : (A -> A) -> endo A`) instantiated at a function type: the
    argument's nested binders must stay curried to match the field's
    `std::function<F(F)>` type. *)

Module ParamInductiveFnInstantiation.
Inductive endo (A : Type) : Type := E : (A -> A) -> endo A.
Definition run {A} (e : endo A) (x : A) : A := match e with E _ f => f x end.
Definition d : endo (nat -> nat) := E _ (fun g => fun n => g (g n)).
Definition go : nat := run d (fun n => n + 1) 0.
End ParamInductiveFnInstantiation.
Crane Extraction "param_inductive_fn_instantiation" ParamInductiveFnInstantiation.
