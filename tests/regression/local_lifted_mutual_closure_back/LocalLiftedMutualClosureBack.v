From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A lifted local mutual group ([local_lifted_mutual]) whose member [f]
    passes its partner [g] a lambda over its own callable, and [g] passes
    it back to [f].  A lambda in a function template has a new closure type
    in every instantiation, so were [g] to deduce its callable, [f<T1, L1>]
    would instantiate [g<T1, L2>], whose callable [f] deduces, whose lambda
    is [L3], and so on without end.  Of a lifted local group only a
    self-call was looked at ([detect_non_forwarded_params_fix]); a partner's
    closure is weighed as a top-level group's is
    ([closure_feedback_params], [mutual_lambda_other_instance]): [g] takes
    a [crane::fn], [f] keeps deducing. *)

Module LocalLiftedMutualClosureBack.

  Definition run (k : nat) (n : nat) : nat :=
    let fp := fix f (A : Type) (h : A -> nat) (y : A) (n : nat) : nat :=
      match n with
      | O => h y
      | S m => g A (fun b => h b + 1) y m
      end
    with g (A : Type) (h : A -> nat) (x : A) (n : nat) : nat :=
      match n with
      | O => h x + k
      | S m => f A h x m
      end
    for f in
    fp (list nat) (@length nat) [1; 2; 3] n + fp bool (fun b => if b then 1 else 2) true n.

End LocalLiftedMutualClosureBack.

Crane Extraction "local_lifted_mutual_closure_back" LocalLiftedMutualClosureBack.
