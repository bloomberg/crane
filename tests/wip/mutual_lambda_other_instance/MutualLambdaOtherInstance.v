From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** [f] calls its partner [g] at another instance, [g bool], than its own,
    passing a lambda over [bool].  Type reconstruction solves a call within
    a recursive group at the group's own variables, so the lambda's binder
    is typed at [f]'s variable: [[](const T1 &b) { if (b) ... }], which does
    not compile once [f] is called at a list.  The call itself is written
    at [bool] ([g<bool>]); only what it reconstructs inside the group is
    not.  [splice_partner_other_instance] is the same pair with a named
    function, which has no binder to type. *)

Module MutualLambdaOtherInstance.

  Fixpoint f (A : Type) (h : A -> nat) (y : A) (n : nat) : nat :=
    match n with
    | O => h y
    | S m => g bool (fun b => if b then 10 else 20) true m
    end
  with g (A : Type) (h : A -> nat) (x : A) (n : nat) : nat :=
    match n with
    | O => h x + 1
    | S m => f A h x m
    end.

  Definition run (n : nat) : nat := f (list nat) (@length nat) [1; 2; 3] n.

End MutualLambdaOtherInstance.

Crane Extraction "mutual_lambda_other_instance" MutualLambdaOtherInstance.
