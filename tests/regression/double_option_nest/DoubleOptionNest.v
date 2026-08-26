(* Regression: no iterative destructor drain when the recursive occurrence sits under
   two layers of [option].

   [classify_ml_self_ref] in "gen_decls.ml" recognises a self-reference under a
   single mediating [option], but [option (option t)] falls through to [`None],
   so [~t()] gets no worklist drain and destruction recurses once per level.
   A 300k-deep value overflows the stack on [delete].

   Distinct from [option_deep_drain], which nests through a *single* [option]
   inside a user inductive. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Module DoubleOptionNest.
Inductive t : Type := node : nat -> option (option t) -> t.
Definition wrap (k : nat) (acc : t) : t := node k (Some (Some acc)).
Definition empty : t := node 0 None.
Definition peek (x : t) : nat :=
  match x with
  | node k o => match o with
                | None => k
                | Some i => match i with None => k + 1 | Some u =>
                    match u with node j _ => k + j end end
                end
  end.
End DoubleOptionNest.
Crane Extraction "double_option_nest" DoubleOptionNest.
