(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [translate inr1] point-free between aliases of [itree] at sums of
    families -- Vellvm's [withCall : MCFGtop ~> CFGtop := translate inr1].
    The source family is erased in [translate]'s type arguments; the tree
    being translated names it, through the alias. *)

From Stdlib Require Import List.
From ITree Require Import ITree.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
Import ITreeNotations.

Module TranslateAliasSource.
  Variant AE : Type -> Type := A : AE nat.
  Variant BE : Type -> Type := B : BE nat.
  Variant CE : Type -> Type := C : CE nat.
  Definition SrcE := AE +' BE.
  Definition DstE := CE +' SrcE.
  Definition SrcTop := itree SrcE.
  Definition DstTop := itree DstE.

  Definition lift : SrcTop ~> DstTop := translate inr1.

  Definition prog : SrcTop nat := Tau (Vis (inl1 A) (fun x => Ret (x + 1))).

  Fixpoint run (fuel : nat) (t : DstTop nat) : nat :=
    match fuel with
    | O => 0
    | S f => match observe t with
             | RetF r => r
             | TauF t' => run f t'
             | VisF e k => match e with
                           | inr1 (inl1 a) =>
                               match a in AE T return (T -> DstTop nat) -> nat with
                               | A => fun k => run f (k 41)
                               end k
                           | _ => 0
                           end
             end
    end.

  Definition result : nat := run 10 (lift _ prog).
End TranslateAliasSource.

Crane Extraction "translate_alias_source" TranslateAliasSource.
