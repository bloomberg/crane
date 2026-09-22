From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
From CraneTestsRegression Require Import eta_expanded_class_method_param_erased.Cls.

(** A concrete carrier.  The instance's [add] takes [list (nat * nat)], not the
    class's abstract [M]. *)
#[global] Instance map_alist : Map nat nat (list (nat * nat)) :=
  { empty := nil
  ; add k v m := cons (k, v) m
  }.
