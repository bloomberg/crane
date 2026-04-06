From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane Loopify.

Module DeepDestruct.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A}.

(** Tail-recursive list builder — should compile to a loop. *)
Fixpoint build_aux (n : nat) (acc : mylist nat) : mylist nat :=
  match n with
  | O => acc
  | S n' => build_aux n' (mycons n acc)
  end.

Definition build (n : nat) : mylist nat := build_aux n mynil.

(** Simple accessor to observe the result. *)
Definition head_or_zero (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons x _ => x
  end.

End DeepDestruct.

Crane Extraction "deep_destruct" DeepDestruct.
