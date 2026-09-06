(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [eq_rect] transporting along an equation between a computed type and a
    concrete one.  The computed type is spelled as a template argument at the
    call, but a type-level definition has no C++ declaration, so the name is
    undeclared. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.

Module EqRectTransport.
Definition cast (A B : Type) (H : A = B) (a : A) : B := eq_rect A (fun T => T) a B H.
Definition run : nat := cast nat nat eq_refl 5.
Definition idty (n : nat) : Type := nat.
Definition run2 : nat := cast (idty 3) nat eq_refl 7.
End EqRectTransport.

Crane Extraction "eq_rect_transport" EqRectTransport.run EqRectTransport.run2.
