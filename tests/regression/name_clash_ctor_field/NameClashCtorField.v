From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module NameClashCtorField.

(** Constructor parameters named to clash with Crane-generated names. *)

(** Fields named like structured binding names: d_a0, d_a1 *)
Inductive clash1 : Type :=
| C1 : forall (d_a0 : nat) (d_a1 : nat), clash1.

Definition sum_clash1 (x : clash1) : nat :=
  match x with
  | C1 a b => a + b
  end.

(** Field named like the scrutinee variable *)
Inductive clash2 : Type :=
| C2a : forall (v : nat), clash2
| C2b : forall (result : nat), clash2.

Definition get_clash2 (x : clash2) : nat :=
  match x with
  | C2a v => v
  | C2b r => r
  end.

(** Two constructors with fields, match on both in sequence *)
Inductive pair_ind : Type :=
| MkPair : nat -> nat -> pair_ind.

Definition swap_pair (p : pair_ind) : pair_ind :=
  match p with
  | MkPair a b => MkPair b a
  end.

(** Nested match where inner and outer have same-named fields *)
Inductive box : Type :=
| Box : pair_ind -> box
| EmptyBox : box.

Definition unbox_sum (b : box) : nat :=
  match b with
  | EmptyBox => 0
  | Box p =>
    match p with
    | MkPair a b => a + b
    end
  end.

End NameClashCtorField.

Crane Extraction "name_clash_ctor_field" NameClashCtorField.
