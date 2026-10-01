From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Class Functorish (F : Type -> Type) : Type :=
  fmapish : forall A B, (A -> B) -> F A -> F B.
Arguments fmapish {F _ A B}.

#[global] Instance Functorish_option : Functorish option | 50 :=
  fun A B f o => match o with Some a => Some (f a) | None => None end.

Class Prov (N : Set) : Type := {
  (* The Vellvm shape: an instance method whose body is a point-free [fmap]
     applied to a singleton-list lambda. *)
  aid_to_prov : option N -> option (list N)
}.

#[global] Instance Prov_nat : Prov nat | 50 := {
  aid_to_prov aid := fmapish (fun x => [x]) aid
}.

Definition plain (o : option nat) : option (list nat) := fmapish (fun x => [x]) o.
Definition run (o : option nat) : option (list nat) := aid_to_prov o.

Crane Extraction "dropped_binder_in_instance_method" run plain.
