From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** [f] calls its partner [g] at another instance, [g bool], than its own.
    Type reconstruction solved a call within a recursive group at the
    group's own variables, so the call's instantiation read as none; only
    the type it is written at said otherwise.  Splicing [g]'s body into [f]
    there wrote it at [f]'s variable -- [T1 x = true] -- and its call of [f]
    back became a turn of [f]'s loop passing [f]'s parameters a [bool]: no
    C++ for [f] at a list.  Neither is spliced into the other. *)

Module SplicePartnerOtherInstance.

  Definition weight (b : bool) : nat := if b then 10 else 20.

  Fixpoint f (A : Type) (h : A -> nat) (y : A) (n : nat) : nat :=
    match n with
    | O => h y
    | S m => g bool weight true m
    end
  with g (A : Type) (h : A -> nat) (x : A) (n : nat) : nat :=
    match n with
    | O => h x + 1
    | S m => f A h x m
    end.

  Definition run (n : nat) : nat := f (list nat) (@length nat) [1; 2; 3] n.

End SplicePartnerOtherInstance.

Set Crane Loopify.
Crane Extraction "splice_partner_other_instance" SplicePartnerOtherInstance.
