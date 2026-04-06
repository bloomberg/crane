From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module DeepApp.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A}.

(** Tail-recursive builder — loopified. *)
Fixpoint build (n : nat) (acc : mylist nat) : mylist nat :=
  match n with
  | O => acc
  | S n' => build n' (mycons n acc)
  end.

(** Recursive app — NOT tail-recursive, so loopification won't help
    unless TMC kicks in.  Even with TMC, the destructor chain for
    the result is still deep. *)
Fixpoint app {A : Type} (l1 l2 : mylist A) : mylist A :=
  match l1 with
  | mynil => l2
  | mycons x xs => mycons x (app xs l2)
  end.

(** Recursive map — same issue. *)
Fixpoint map {A B : Type} (f : A -> B) (l : mylist A) : mylist B :=
  match l with
  | mynil => mynil
  | mycons x xs => mycons (f x) (map f xs)
  end.

(** Identity map to force traversal. *)
Definition map_id (l : mylist nat) : mylist nat := map (fun x => x) l.

(** Append two lists. *)
Definition append_lists (l1 l2 : mylist nat) : mylist nat := app l1 l2.

Definition head_or_zero (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x _ => x
  end.

Fixpoint length {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ xs => S (length xs)
  end.

End DeepApp.

Crane Extraction "deep_app" DeepApp.
