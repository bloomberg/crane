(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A pattern lambda handed to another instance's method inside an
    instance's method, as Vellvm's [TFunctor_phi] does: the lambda maps
    pairs of the input element type to pairs of the output one, and its
    binder must be typed by the input. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.

Module PatternLambdaThroughInstance.

Class Endo (T : Type) := endo : T -> T.
Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

#[global] Instance TFunctor_list : TFunctor list := List.map.

Inductive exp (T : Set) : Set := Lit : T -> exp T.
Arguments Lit {T}.

#[global] Instance TFunctor_exp : TFunctor exp :=
  fun U V f e => match e with Lit x => Lit (f x) end.

Inductive phi (T : Set) : Set := Phi : T -> list (nat * exp T) -> phi T.
Arguments Phi {T}.

#[global] Instance TFunctor_phi `{Endo nat} `{TFunctor exp} : TFunctor phi :=
  fun U V f '(Phi t args) =>
    Phi (f t) (tfmap (fun '(id, e) => (endo id, tfmap f e)) args).

#[global] Instance Endo_nat : Endo nat := S.

Definition p0 : phi nat := Phi 1 ((2, Lit 3) :: (4, Lit 5) :: nil).
Definition p1 : phi bool := tfmap (fun n => Nat.eqb n 3) p0.

Definition result : nat :=
  match p1 with
  | Phi b args =>
      (if b then 100 else 0)
      + List.fold_left (fun (acc : nat) '((id, e) : nat * exp bool) => match e with Lit x => acc + id + (if x then 10 else 0) end) args 0
  end.

End PatternLambdaThroughInstance.

Crane Extraction "pattern_lambda_through_instance" PatternLambdaThroughInstance.
