From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module TypeLevelFixpointArity.

(** A type computed by a fixpoint over a [nat] loses its arity, so values
    built at one arity are read back at another. *)
Fixpoint nfun (n : nat) : Type :=
  match n with O => nat | S k => nat -> nfun k end.

Fixpoint constN (n : nat) (v : nat) : nfun n :=
  match n with
  | O => v
  | S k => fun _ => constN k v
  end.

Definition apply1 (f : nfun 1) (x : nat) : nat := f x.
Definition apply2 (f : nfun 2) (x y : nat) : nat := f x y.

Definition total : nat :=
  (constN 0 7) + apply1 (constN 1 8) 0 + apply2 (constN 2 9) 0 0.

End TypeLevelFixpointArity.
Crane Extraction "type_level_fixpoint_arity" TypeLevelFixpointArity.
