From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsRegression Require Import collision_wrapper_drops_child_module.Cls.
From CraneTestsRegression Require Import collision_wrapper_drops_child_module.AstLike.

(** Forces [ident] into the extracted unit so its C++ name [Ident] is there to
    collide with [AstLike]'s child module. *)
Definition to_ident (k : raw_id) : ident :=
  match k with Name n => Global n | Anon n => Local n end.

(** The colliding child's member and the non-colliding child's member, named
    from another file in the same expression.  [RawIDOrd.eq_dec] is the
    control: it is the same construction under a name nothing collides with,
    so it must come out qualified with the child either way. *)
Definition both (k : raw_id) : ident * (bool * bool * bool) :=
  (to_ident k,
   (Ident.eq_dec (tag k) 1, RawIDOrd.eq_dec (tag k) 1, Ord.compare k k)).

Crane Extraction "collision_wrapper_drops_child_module" both.
