(* Regression: recursion nested inside [prod] gets no iterative drain.

   [N : (t * nat) -> t] hides the self-reference behind [std::pair], which the
   drain classifier does not look through, so destroying a deep chain recurses
   ~t -> ~pair<t, uint64_t> -> ~t -> ...

   The traversal uses a match rather than [fst] so the test isolates the drain
   from the projection bug in [prod_fst_projection]. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Set Crane Loopify.
Module ProdDrain.
Inductive t : Type := L : t | N : (t * nat) -> t.
Fixpoint build (n : nat) (acc : t) : t :=
  match n with O => acc | S m => build m (N (acc, n)) end.
Fixpoint depth (x : t) : nat :=
  match x with L => 0 | N p => match p with (u, _) => S (depth u) end end.
Definition go (n : nat) : nat := depth (build n L).
End ProdDrain.
Crane Extraction "prod_drain" ProdDrain.
