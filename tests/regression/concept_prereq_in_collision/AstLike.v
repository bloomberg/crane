(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat.
From CraneTestsRegression Require Import concept_prereq_in_collision.Cls.

(** Everything this file declares is written inside the struct [AstLike],
    its child module [Ident] colliding with [Cls.ident], and [Keyed]'s
    concept at the top of the file.  The concept names [key], which as a
    member of [AstLike] cannot come first: the struct's members name the
    concept.  [key] moves out ahead of the concept, the only order in which
    it can be read, and [AstLike] keeps a member alias of it, through which
    [AstLike::key], as [User] spells it, still names it. *)

Definition key : Set := nat.

Class Keyed (A : Set) := { key_of : A -> key }.

Module Ident.
  Definition eq (a b : nat) : bool := Nat.eqb a b.
End Ident.

#[global] Instance keyed_nat : Keyed nat := {| key_of := fun n => n |}.

Definition same {A : Set} `{Keyed A} (x y : A) : bool := Ident.eq (key_of x) (key_of y).
