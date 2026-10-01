From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat.
From CraneTestsRegression Require Import collision_wrapper_drops_child_module.Cls.

Inductive raw_id : Set := Name (n : nat) | Anon (n : nat).

Module Type MiniTyp.
  Parameter t : Set.
  Parameter eq_dec : t -> t -> bool.
End MiniTyp.

Module Make_UDT (T : MiniTyp).
  Definition t : Set := T.t.
  Definition eq_dec : t -> t -> bool := T.eq_dec.
End Make_UDT.

Module IdentDec <: MiniTyp.
  Definition t : Set := nat.
  Definition eq_dec (a b : nat) : bool := Nat.eqb a b.
End IdentDec.

Module RawIDOrdDec <: MiniTyp.
  Definition t : Set := nat.
  Definition eq_dec (a b : nat) : bool := Nat.eqb a b.
End RawIDOrdDec.

(** The colliding child, as a functor application -- Vellvm's exact shape.
    The application is load-bearing: an inline [Module Ident. ... End Ident.]
    flattens correctly and the test would pass while testing nothing. *)
Module Ident := Make_UDT(IdentDec).

(** Control: same construction, non-colliding name. *)
Module RawIDOrd := Make_UDT(RawIDOrdDec).

Definition tag (k : raw_id) : nat := match k with Name n => n | Anon n => n end.

(** Second manifestation: an ordinary (non-colliding, non-functor) child whose
    members refer to each other, as Vellvm's [AstLib.RawIDOrd.compare] calls
    its sibling [cmp].  The body must come out [Ord::cmp]; a bare [cmp(x, y)]
    means no wrapper formed and the file is testing nothing. *)
Module Ord.
  Definition t : Set := raw_id.
  Definition cmp (x y : t) : bool := Nat.eqb (tag x) (tag y).
  Definition compare (x y : t) : bool := negb (cmp x y).
End Ord.
