From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** [f] calls itself at [bool], not at its own [A], passing a lambda over
    [bool].  Extraction instantiates the call at [bool], so the lambda is
    [[](bool b)] and translation writes the call [f<bool>].  The function's
    generation replaces every other reference to itself with the reference
    at its own template parameters ([glob_subst_stmt] with [rec_call] in
    gen_functions.ml); this one it spares, since the call's use solves [A]
    to a ground type ([other_instance_self_calls]).  Respelled [f<T1>], it
    would take no lambda over [bool] once [f] is called at a list.  The same
    pair across two functions is [mutual_lambda_ground_instance]. *)

Module SelfCallOtherInstance.

  Fixpoint f (A : Type) (h : A -> nat) (y : A) (n : nat) : nat :=
    match n with
    | O => h y
    | S m => f bool (fun b => if b then 10 else 20) true m
    end.

  Definition run (n : nat) : nat := f (list nat) (@length nat) [1; 2; 3] n.

End SelfCallOtherInstance.

Crane Extraction "self_call_other_instance" SelfCallOtherInstance.
