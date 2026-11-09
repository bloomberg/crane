From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** [f] calls its partner [g] at [bool], not at its own [A], passing a
    lambda over [bool].  Extraction typed a call within the recursive group
    at the group's own variables whatever it was written at, so the
    lambda's binder took [f]'s variable: [[](const T1 &b) { if (b) ... }],
    no C++ once [f] is called at a list.  A type argument written as a
    ground type instantiates the partner like any other constant.  [g]
    calls back with a named function, whose type is the same at every
    instance; a lambda there is [mutual_lambda_other_instance]. *)

Module MutualLambdaGroundInstance.

  Definition dbl (k : nat) : nat := k + k.

  Fixpoint f (A : Type) (h : A -> nat) (y : A) (n : nat) : nat :=
    match n with
    | O => h y
    | S m => g bool (fun b => if b then 10 else 20) true m
    end
  with g (A : Type) (h : A -> nat) (x : A) (n : nat) : nat :=
    match n with
    | O => h x + 1
    | S m => f nat dbl m m
    end.

  Definition run (n : nat) : nat := f (list nat) (@length nat) [1; 2; 3] n.

End MutualLambdaGroundInstance.

Crane Extraction "mutual_lambda_ground_instance" MutualLambdaGroundInstance.
