From Crane Require Import Mapping.Std.

(** The inductive whose name collides with [AstLib]'s first child, which is
    what forces [AstLib] to be emitted as a wrapper struct at all. *)
Inductive Collider : Set := | Tag0 : Collider | Tag1 : nat -> Collider.
