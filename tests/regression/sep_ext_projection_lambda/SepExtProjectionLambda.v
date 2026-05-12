(* Regression: record projections used as first-class function values
   inside a functor (separate extraction) must render as lambdas since
   no standalone function definition is emitted.  Previously Crane
   generated D::Defs::prediction which didn't resolve because the
   projection was only emitted as a struct field. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module Type Sig.
  Parameter A : Type.
End Sig.

Module Worker (S : Sig).

  Record item := mk_item {
    label : nat;
    payload : S.A;
  }.

  Definition get_label (x : item) : nat := label x.

  Definition all_labels (xs : list item) : list nat :=
    map label xs.

  Fixpoint find_label (target : nat) (xs : list item) : option S.A :=
    match xs with
    | nil => None
    | x :: rest =>
      if Nat.eqb (label x) target
      then Some (payload x)
      else find_label target rest
    end.

End Worker.

Crane Separate Extraction Worker.
