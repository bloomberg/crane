(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** A product's conversion to another instantiation exists exactly where
    every field converts: one constructor holds them all.  A spine's
    conversion takes no native frame per cell. *)
Module ProductConversion.

Inductive pair (A B : Type) : Type := mk : A -> B -> pair A B.
Arguments mk {A B} a b.

Record tagged (A : Type) : Type := { tag : nat; payload : A }.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.
Arguments nil {A}.
Arguments cons {A} a l.

Definition swap {A B : Type} (p : pair A B) : pair B A :=
  match p with mk a b => mk b a end.

End ProductConversion.

Crane Extraction "product_conversion" ProductConversion.
