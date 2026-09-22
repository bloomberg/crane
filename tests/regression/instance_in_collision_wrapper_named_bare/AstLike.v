From Crane Require Import Mapping.Std.
From Stdlib Require Import PeanoNat.
From CraneTestsRegression Require Import instance_in_collision_wrapper_named_bare.Cls.

Inductive raw_id : Set := Name (n : nat) | Anon (n : nat).

Definition raw_id_eqb (a b : raw_id) : bool :=
  match a, b with
  | Name n, Name m => Nat.eqb n m
  | Anon n, Anon m => Nat.eqb n m
  | _, _ => false
  end.

(** A child module whose capitalised name [Ident] is already the C++ name of
    [Cls.ident].  This is the collision, and it is the only reason this file
    becomes a struct.  Vellvm's [AstLib.v] plays the same role with
    [Module Ident := Make_UDT(IdentDec)] against [LLVMAst]'s [ident]. *)
Module Ident.
  Definition eq (a b : nat) : bool := Nat.eqb a b.
End Ident.

(** A file-level instance, a sibling of the colliding child.  It is emitted
    inside the wrapper struct along with everything else this file declares,
    and a use of it from another file must say so. *)
#[global] Instance eq_dec_raw_id : Dec raw_id := {| dec := raw_id_eqb |}.

Definition describe (k : raw_id) : nat :=
  match k with Name n => if Ident.eq n n then n else 0 | Anon n => n end.

(** The control.  Two arguments, so it is not methodified onto a datatype; it
    stays a member of the wrapper struct exactly as the instance does, and it
    is named from the same use site.  It must come out qualified. *)
Definition combine (a b : nat) : nat := a + b.
