(** Crane bug: a module absorbed into a collision wrapper is qualified only
    where it is named through [::].

    A file whose child module's name collides with an inductive elsewhere is
    emitted as a struct named after the file, and a non-colliding sibling is
    nested inside it.  A reference spelling that sibling [RawIDOrd::eq_dec]
    reaches [wrapper_qualify_name]'s already-qualified branch and comes out
    right.  A reference that names the sibling *bare* -- as a functor argument,
    a template argument, a type -- never reaches that branch at all.

    Seen in Vellvm, where [using RM = Make<RawIDOrd>;] does not compile while
    [AstLib::RawIDOrd::eq_dec] beside it does. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import Arith PeanoNat.
From CraneTestsRegression Require Import bystander_named_bare.Rid.
From CraneTestsRegression Require Import bystander_named_bare.Ord.

(** Colliding: its capitalised label is [Coll]'s inductive, so it fires the
    wrapper -- and the printer flattens it into the wrapper's body. *)
Module Collider.
  Definition pick (a b : nat) : nat := if Nat.leb a b then b else a.
End Collider.

(** Not colliding: the printer nests it inside the same wrapper struct. *)
Module RawIDOrd <: Ord.
  Definition t : Set := raw_id.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y} := raw_id_dec.
End RawIDOrd.
