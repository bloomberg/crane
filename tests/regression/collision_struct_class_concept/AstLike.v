(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat.
From CraneTestsRegression Require Import collision_struct_class_concept.Cls.

(** [Keyed] is declared in a file whose child module [Ident] collides
    with [Cls.ident], so everything the file declares is written inside the
    struct [AstLike].  A concept cannot be a member, and the class's
    declaration generates none inside a struct, the module frame around a
    class otherwise declaring it at file scope -- but this struct has no
    such frame.  Its concept is generated and declared at the top of the
    file, as a nested module's are, where the instance's assertion and
    [same]'s constraint inside the struct can name it. *)

Class Keyed (A : Set) := { key_of : A -> nat }.

Module Ident.
  Definition eq (a b : nat) : bool := Nat.eqb a b.
End Ident.

#[global] Instance keyed_nat : Keyed nat := {| key_of := fun n => n |}.

Definition same {A : Set} `{Keyed A} (x y : A) : bool := Ident.eq (key_of x) (key_of y).
