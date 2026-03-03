(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Test singleton records (records with single field - special case) *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module SingletonRecord.

(* Singleton record with one field *)
Record wrapper : Type := { value : nat }.

(* Create wrapper *)
Definition wrapped_five : wrapper := {| value := five |}.

(* Access field *)
Definition get_value (w : wrapper) : nat := value w.

(* Alternative accessor syntax *)
Definition get_value2 (w : wrapper) : nat := w.(value).

(* Pattern match on singleton record *)
Definition unwrap (w : wrapper) : nat :=
  match w with
  | {| value := n |} => n
  end.

(* Function on wrapped value *)
Definition double_wrapped (w : wrapper) : wrapper :=
  {| value := Nat.mul two (value w) |}.

(* Polymorphic singleton record *)
Record box (A : Type) : Type := { contents : A }.

Arguments contents {A} _.

Definition boxed_three : box nat := {| contents := three |}.
Definition unbox {A : Type} (b : box A) : A := contents b.

(* Nested singleton records *)
Definition nested_box : box (box nat) := {| contents := boxed_three |}.
Definition double_unbox : nat := contents (contents nested_box).

(* Singleton record with function field *)
Record fn_wrapper : Type := { fn : nat -> nat }.

Definition my_fn_wrapper : fn_wrapper := {| fn := Nat.add one |}.
Definition apply_wrapped (w : fn_wrapper) (n : nat) : nat := (fn w) n.

(* Test values *)
Definition test_get := get_value wrapped_five.
Definition test_get2 := get_value2 wrapped_five.
Definition test_unwrap := unwrap wrapped_five.
Definition test_double := value (double_wrapped wrapped_five).
Definition test_unbox := unbox boxed_three.
Definition test_double_unbox := double_unbox.
Definition test_fn := apply_wrapped my_fn_wrapper seven.

End SingletonRecord.

Crane Extraction "singleton_record" SingletonRecord.
