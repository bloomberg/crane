From Crane Require Import Mapping.Std.

(** A class with an abstract carrier [M], as Vellvm's [Map] has an abstract
    [map].  [add] takes the carrier as its last argument; that is the parameter
    whose type goes missing. *)
Class Map (K V M : Set) :=
  { empty : M
  ; add : K -> V -> M -> M
  }.
