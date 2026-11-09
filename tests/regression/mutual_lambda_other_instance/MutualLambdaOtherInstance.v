From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** [f] calls its partner [g] at another instance, [g bool], than its own,
    passing a lambda over [bool], and [g] passes it back to [f].  A lambda
    in a function template has a new closure type in every instantiation, so
    were [g] to take it as a deduced callable, [g<bool, L1>] would
    instantiate [f<bool, L1 &>], whose lambda [L2] instantiates [g<bool,
    L2>], and so on without end.  The lambda's type flows back into the
    instantiation that makes it, so [g] takes it as a [crane::fn]
    ([partner_closure_params]).  With a named callback instead the cycle
    closes and [g] deduces it ([splice_partner_other_instance]), as it does
    where [g] does not pass it back ([mutual_lambda_ground_instance]). *)

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
