(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat.
From CraneTestsWIP Require Import collision_struct_class_concept.Cls.

(** Known bug: [Keyed] is declared in a file whose child module [Ident]
    collides with [Cls.ident], so everything the file declares is written
    inside the struct [AstLike].  A concept cannot be a member, and the
    class's declaration generates none inside a struct, expecting the
    module frame around it to declare it at file scope -- but this struct
    has no such frame, so no concept [Keyed] is declared at all, while the
    instance's assertion and [same]'s constraint name it.

    Once it is declared, at the top of the file with the others, a type it
    names that the file declares -- [Definition key := nat] spelling the
    field [key_of : A -> key] -- is a member of [AstLike], which cannot
    come first: its members name the concept.  The file's layout moves
    such a type to the top as well, out of the struct (a violation under
    [CRANE_CHECK_IR], "concept prerequisites"); a use from another file,
    spelled [AstLike::key], would then name nothing. *)

Class Keyed (A : Set) := { key_of : A -> nat }.

Module Ident.
  Definition eq (a b : nat) : bool := Nat.eqb a b.
End Ident.

#[global] Instance keyed_nat : Keyed nat := {| key_of := fun n => n |}.

Definition same {A : Set} `{Keyed A} (x y : A) : bool := Ident.eq (key_of x) (key_of y).
