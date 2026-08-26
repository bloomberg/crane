(* Regression: the [prod_fst_projection] bug through the other projection.

   [snd p] on a [std::shared_ptr<std::pair<...>>] field prints as
   [*a0.second] rather than [( *a0 ).second]:

     error: no member named 'second' in
            'std::shared_ptr<std::pair<uint64_t, ProdSndProjection::t>>'

   Kept separate from [prod_fst_projection] because the two projections go
   through different code paths and a fix for one need not cover the other. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module ProdSndProjection.
Inductive t : Type := L : t | N : (nat * t) -> t.
Fixpoint depth (x : t) : nat :=
  match x with L => 0 | N p => S (depth (snd p)) end.
Definition go : nat := depth (N (1, N (2, L))).
End ProdSndProjection.
Crane Extraction "prod_snd_projection" ProdSndProjection.
