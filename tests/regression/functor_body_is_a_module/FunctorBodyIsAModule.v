(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A functor whose body is a module rather than a structure: [Id] is its
    own parameter and [Const] is [Nat_T] whatever it is applied to.  Each
    becomes a struct template deriving from that module, as a functor
    whose body applies another functor does, so its applications have the
    module's members. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.

Module FunctorBodyIsAModule.

Module Type T.
  Parameter t : Type.
  Parameter z : t.
End T.

Module Nat_T <: T.
  Definition t := nat.
  Definition z := 3.
End Nat_T.

Module Seven <: T.
  Definition t := nat.
  Definition z := 7.
End Seven.

Module Id (X : T) := X.
Module Const (X : T) := Nat_T.

Module I := Id Seven.
Module C := Const Seven.

Definition from_id : nat := I.z.
Definition from_const : nat := C.z.

End FunctorBodyIsAModule.

Crane Extraction "functor_body_is_a_module" FunctorBodyIsAModule.
