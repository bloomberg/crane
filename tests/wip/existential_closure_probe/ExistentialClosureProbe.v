From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ExistentialClosureProbe.

(** Type-indexed inductive wrapping a value of erased type.
    The type index A is erased to std::any by Crane.
    Values stored in the wrapper must be recovered via any_cast. *)

Inductive wrap : Set -> Type :=
  | Wrap : forall (A : Set), A -> wrap A.

Definition unwrap {A : Set} (w : wrap A) : A :=
  match w with
  | Wrap _ x => x
  end.

(** Pack a closure into a type-erased wrapper. *)
Definition pack_fn (base : nat) : wrap (nat -> nat) :=
  Wrap (nat -> nat) (fun x => x + base).

(** Unpack and apply. *)
Definition apply_packed (w : wrap (nat -> nat)) (x : nat) : nat :=
  unwrap w x.

(** test1: pack base=10, apply to 5. Expected: 15. *)
Definition test1 : nat :=
  apply_packed (pack_fn 10) 5.

(** test2: Pack and unpack through a let binding.
    base=42, apply to 0. Expected: 42. *)
Definition test2 : nat :=
  let p := pack_fn 42 in
  apply_packed p 0.

(** Store a closure that captures another closure. *)
Definition pack_composed (a b : nat) : wrap (nat -> nat) :=
  let f := fun x => x + a in
  let g := fun x => f x * b in
  Wrap (nat -> nat) g.

(** test3: a=3, b=2, g(5) = (5+3)*2 = 16. *)
Definition test3 : nat :=
  apply_packed (pack_composed 3 2) 5.

End ExistentialClosureProbe.

Crane Extraction "existential_closure_probe" ExistentialClosureProbe.
