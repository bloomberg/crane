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
  (** The first element of the pair. *)
  fst : A;
  (** The second element of the pair. *)
  snd : B
}.

(** [mylist] is a polymorphic list type. *)
Inductive mylist (A : Type) : Type :=
  (** The empty list. *)
  | mynil : mylist A
  (** Cons cell: an element followed by the rest of the list. *)
  | mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A} a l.

Definition no_doc_comment (x : nat) : nat := x.

(** The identity function: returns its argument unchanged. *)
Definition identity {A : Type} (x : A) : A := x.

(** [double n] returns [2 * n]. *)
Definition double (n : nat) : nat := add n n.

(** A simple color enumeration. *)
Inductive color : Type :=
  (** Red color. *)
  | red
  (** Green color. *)
  | green
  (** Blue color. *)
  | blue.

End DocComments.

Crane Extraction "doc_comments" DocComments.
