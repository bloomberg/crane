From Crane Require Import Mapping.Std.
From CraneTestsWIP Require Import noncolliding_child_unregistered.Coll.
From CraneTestsWIP Require Import noncolliding_child_unregistered.Rid.
From CraneTestsWIP Require Import noncolliding_child_unregistered.AstLib.

(** The bystander, seen from outside: the one reference of the four that comes
    out unqualified. *)
Definition via_non_colliding (a b : raw_id) : bool :=
  if AstLib.RawIDOrd.eq_dec a b then true else false.

Definition via_colliding (a b : nat) : nat := AstLib.Collider.pick a b.

Definition via_file (a b : raw_id) : bool := AstLib.eq_dec_raw_id a b.

(** Keeps [Coll.Collider] alive, so the collision it causes is real. *)
Definition keep_coll (r : Coll.Collider) : nat :=
  match r with Coll.Tag0 => 0 | Coll.Tag1 n => n end.

Crane Extraction "noncolliding_child_unregistered"
  via_non_colliding via_colliding via_file keep_coll.
