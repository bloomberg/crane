(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A file module that becomes a wrapper struct of the extracted unit, with an
    instance whose method lifts a polymorphic local fixpoint. *)

From Stdlib Require Import List.
Import ListNotations.

Class Sized (A : Type) := { size : A -> nat }.

Definition twice (n : nat) : nat := n + n.

#[export] Instance sized_pair : Sized (list nat * list bool) := {
  size := fun p =>
    let fix len {B : Type} (xs : list B) : nat :=
      match xs with [] => 0 | _ :: r => S (len r) end in
    len (fst p) + len (snd p) }.
