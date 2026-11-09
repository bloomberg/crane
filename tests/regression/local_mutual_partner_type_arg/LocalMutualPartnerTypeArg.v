From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

(** A local mutual group whose partner [g], not the member [f] the group is
    projected to, takes a type argument.  Dummy elimination
    ([kill_dummy_fix]) dropped the erased binders of the projected member
    alone, and only where it had some, so [g] kept a parameter for [A]
    while [f]'s call to it, its dummy argument dropped, passed none: [g]
    took one argument more than it was given.  Every member's erased
    binders go, each member's calls adjusted. *)

Module LocalMutualPartnerTypeArg.

  Definition run (k : nat) (n : nat) : nat :=
    (fix f (n : nat) : nat :=
      match n with
      | O => 1
      | S m => g nat (fun x => x + 1) m m
      end
    with g (A : Type) (h : A -> nat) (x : A) (n : nat) : nat :=
      match n with
      | O => h x
      | S m => f m + 1
      end
    for f) n.

End LocalMutualPartnerTypeArg.

Crane Extraction "local_mutual_partner_type_arg" LocalMutualPartnerTypeArg.
