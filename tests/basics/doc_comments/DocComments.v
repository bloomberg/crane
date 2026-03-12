(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module DocComments.

(** [add] computes the sum of two natural numbers [n] and [m].
    It works by structural recursion on [n]. *)
Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (add p m)
  end.

(** A simple pair holding two values of possibly different types. *)
Record pair (A B : Type) := mkpair {
  fst : A;
  snd : B
}.

(** [mylist] is a polymorphic list type.
    - [mynil] is the empty list.
    - [mycons] prepends an element. *)
Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A} a l.

Definition no_doc_comment (x : nat) : nat := x.

(** The identity function: returns its argument unchanged. *)
Definition identity {A : Type} (x : A) : A := x.

(** [double n] returns [2 * n]. *)
Definition double (n : nat) : nat := add n n.

End DocComments.

Crane Extraction "doc_comments" DocComments.
