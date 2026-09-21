(** Crane bug: a module pulled into a collision wrapper without colliding
    itself is never told the wrapper's name.

    A file whose child module's name collides with an inductive elsewhere is
    emitted as a struct named after the file.  The printer puts every other
    child inside that struct too, rendered normally -- so a non-colliding child
    becomes a properly nested [struct AstLib::RawIDOrd].  But only the
    colliding children are registered as living in the wrapper, so a reference
    from outside spells the bystander [RawIDOrd::eq_dec], with nothing to say
    the [AstLib::].

    Seen in Vellvm, where [Ident] is the collider and [RawIDOrd] the bystander
    that everything references. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import Arith PeanoNat.
From CraneTestsWIP Require Import noncolliding_child_unregistered.Rid.

(** Colliding: its capitalised label is [Coll]'s inductive, so it fires the
    wrapper -- and the printer flattens it. *)
Module Collider.
  Definition pick (a b : nat) : nat := if Nat.leb a b then b else a.
End Collider.

(** Not colliding: the printer nests it inside the same wrapper struct, and the
    registration loop never sees it. *)
Module RawIDOrd.
  Definition t : Set := raw_id.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y} := raw_id_dec.
End RawIDOrd.

(** The file's own top-level declaration: the half that is registered. *)
Definition eq_dec_raw_id (a b : raw_id) : bool :=
  if RawIDOrd.eq_dec a b then true else false.
