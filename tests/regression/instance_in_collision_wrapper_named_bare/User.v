From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
From CraneTestsRegression Require Import instance_in_collision_wrapper_named_bare.Cls.
From CraneTestsRegression Require Import instance_in_collision_wrapper_named_bare.AstLike.
From CraneTestsRegression Require Import instance_in_collision_wrapper_named_bare.Lookup.

(** Forces [ident] into the extracted unit, so that its C++ name [Ident] is
    there for [AstLike]'s child module to collide with. *)
Definition to_ident (k : raw_id) : ident :=
  match k with Name n => Global n | Anon n => Local n end.

(** [assoc] resolves [Dec raw_id] implicitly to [AstLike.eq_dec_raw_id] and
    passes it as a template argument.  [describe] names the same file
    explicitly, at the same site, and is the control. *)
Definition find (k : raw_id) (l : list (raw_id * nat)) : nat * option nat :=
  (describe k, assoc k l).

Definition both (k : raw_id) (l : list (raw_id * nat))
  : ident * (nat * option nat) := (to_ident k, find k l).

(** Instance and control side by side in one statement. *)
Definition both_at_one_site (k : raw_id) (l : list (raw_id * nat))
  : nat * option nat := (combine (describe k) 1, assoc k l).

Crane Extraction "instance_in_collision_wrapper_named_bare"
  both both_at_one_site.
