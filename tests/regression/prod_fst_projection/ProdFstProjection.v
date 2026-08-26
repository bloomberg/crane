(* Regression: [fst] applied to a recursive [prod] field emits an unparenthesised
   dereference, so the member access binds to the pointer.

   [N : (t * nat) -> t] makes the field indirect, so its C++ type is
   [std::shared_ptr<std::pair<t, uint64_t>>].  [fst p] must print as
   [( *a0 ).first]; Crane prints [*a0.first], which C++ parses as
   [*(a0.first)]:

     error: no member named 'first' in
            'std::shared_ptr<std::pair<ProdFstProjection::t, ...>>'

   The same splice for [option]'s match template was fixed by parenthesising
   prefix-operator scrutinees; the [prod] projections were not covered.
   See also [prod_snd_projection]. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Set Crane Loopify.
Module ProdFstProjection.
Inductive t : Type := L : t | N : (t * nat) -> t.
Fixpoint build (n : nat) (acc : t) : t :=
  match n with O => acc | S m => build m (N (acc, n)) end.
Fixpoint depth (x : t) : nat :=
  match x with L => 0 | N p => S (depth (fst p)) end.
Definition go (n : nat) : nat := depth (build n L).
End ProdFstProjection.
Crane Extraction "prod_fst_projection" ProdFstProjection.
