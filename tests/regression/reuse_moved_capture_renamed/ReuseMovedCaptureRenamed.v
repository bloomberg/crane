(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A closure taking by move a pattern variable that translation renames.

    Under Crane Reuse the list [adders] walks is owned, so the closure each
    cell holds takes the tree it closes over by move.  Translation names the
    tree by the field binding the match makes, and renamed the variable
    inside the closure but not the capture moving it: the closure moved a
    name that was not in scope. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
From Crane Require Import Mapping.NatIntStd.

Module ReuseMovedCaptureRenamed.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Definition peek (t : tree) (x : nat) : nat :=
  match t with
  | Leaf => x
  | Node _ v _ => v + x
  end.

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.
Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint adders (ts : mylist tree) : mylist (nat -> nat) :=
  match ts with
  | mynil => mynil
  | mycons t rest => mycons (peek t) (adders rest)
  end.

Fixpoint apply_all (fs : mylist (nat -> nat)) (x : nat) : nat :=
  match fs with
  | mynil => 0
  | mycons f rest => f x + apply_all rest x
  end.

End ReuseMovedCaptureRenamed.

Set Crane Loopify.
Set Crane NonAtomicRc.
Set Crane Reuse.
Crane Extraction "reuse_moved_capture_renamed" ReuseMovedCaptureRenamed.
