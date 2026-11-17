From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** The local version of [mutual_lambda_other_instance]: [f] calls its
    partner [g] at [bool], not at the [list nat] it is entered at, and [g]
    passes the lambda back to [f].  Extraction types a local group's bodies
    at one instance, which would type [f]'s callable over [List] and [g]'s
    over [bool], with no conversion from one to the other.  Instead the
    group's type binders are erased ([Extraction.erased_fix_types]): both
    callables are [crane::fn<uint64_t(crane::obj)>], a closure written at its
    own instance is adapted by [crane_erase_fn], and [g] passes [h] back
    unadapted, as it is already erased. *)

Module LocalMutualPolymorphicRecursion.

  Definition run (n : nat) : nat :=
    (fix f (A : Type) (h : A -> nat) (y : A) (n : nat) : nat :=
      match n with
      | O => h y
      | S m => g bool (fun b => if b then 10 else 20) true m
      end
    with g (A : Type) (h : A -> nat) (x : A) (n : nat) : nat :=
      match n with
      | O => h x + 1
      | S m => f A h x m
      end
    for f) (list nat) (@length nat) [1; 2; 3] n.

End LocalMutualPolymorphicRecursion.

Crane Extraction "local_mutual_polymorphic_recursion" LocalMutualPolymorphicRecursion.
