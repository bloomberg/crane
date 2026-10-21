
From Stdlib Require Import
  Arith.PeanoNat
  Arith.Peano_dec
  Classes.EquivDec
  Init.Peano
  List
  Morphisms
  PrimString
  RelationClasses
  Relation_Definitions
  Setoid
.

From ExtLib Require Import
  CmpDec
  Data.Bool
  Data.List
  Data.Monads.EitherMonad
  Data.Pair
  Data.String
  Data.Option
  Structures.Functor
  Structures.Traversable
  Structures.Reducible
.

(* NOTE: *must* import this before the ITree Eq.Paco2 import.*)
From Paco Require Import paco.

From ITree Require Import
  Basics.HeterogeneousRelations
  Eq.Paco2
  Events.Exception
  Events.FailFacts
  Events.MapDefault
  Events.MapDefaultFacts
  Events.State
  Events.StateFacts
  ITree
  ITreeFacts
.

From Crane Require Import
  Extraction
  Monads.Error
  Monads.ITree
  Monads.Indices
  Monads.MonadFacts
  Monads.STMonad
  Monads.STMonadFacts
  Utils.HAList
  Utils.HMap
.

Import Monads.
Import ListNotations.
Import ProperNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.
From Corelib Require Derive.

(* Tactics for 'stepping through STMonad' instances *)
(* Bind Split tactics *)


(* Ltac bind_split_intros2_refl split_tactic pre_tactic :=
 *   split_tactic ;[ pre_tactic; reflexivity | intros (?, ?) ]
 *   ;cbv beta match.
 * 
 * Ltac bind_split_intros2_refl split_tactic :=
 *   split_tactic ;[ reflexivity | intros (?, ?)]
 *   ;cbv beta match.
 * 
 * Ltac bind_split_intros2 split_tactic pre_tactic :=
 *   split_tactic ;[ pre_tactic | intros (?, ?)]
 *   ;cbv beta match.
 * 
 * Ltac bind_split_intros split_tactic pre_tactic :=
 *   split_tactic ;[ pre_tactic; reflexivity | intros ]
 *   ;cbv beta match.
 * 
 * Ltac bind_split_refl_intros split_tactic :=
 *   split_tactic ;[ reflexivity | intros]
 *   ;cbv beta match. *)

Ltac bind_split_intros split_tactic pre_tactic :=
  split_tactic ;[ pre_tactic | intros ]
  ;cbv beta match.

(* Hints *)
Hint Unfold
  newSTRef
  readSTRef
  writeSTRef
  newArray
  newListArray
  readArray
  writeArray
  getElems
  : monadsimp. 

(* simplify a "leaf" of an itree and apply reflexivity.
   This could be a single event or ret of a pure node, but not tau.
   Applying reflexivity is so we can use it as part of existentially constructing a term.*)
Ltac simp_interp_leaf_refl :=
  autounfold with monadsimp; rewrite interp_st_trigger; cbn; try reflexivity.

Ltac simp_interp_leaf :=
  autounfold with monadsimp; rewrite interp_st_trigger; cbn.

Ltac stforward_inner simp_interp_fun :=
  match goal with
  | [ |- context[ eutt eq (interp_st ?R ?t (ITree.bind ?head ?k) ?lmem) ?goal ] ] =>
    idtac "bind with head:"; idtac head;
    bind_split_intros
      ltac:(eapply (eutt_eq_bind_interp_st _ ltac:(refine_prod)))
      ltac:(simp_interp_fun)
  | [ |- context[ eutt eq (interp_st ?R ?t (bind (ret ?v) ?k) ?lmem) ?goal ] ] =>
    idtac "bind (ret v;...)"; (* TODO: try Monad.bind_ret*? *)
    bind_split_intros
      ltac:(eapply (eutt_eq_bind_interp_st ltac:(refine_prod)))
      ltac:(rewrite interp_st_ret)
  | [ |- context[ eutt eq (interp_st ?R ?t (Ret ?v) ?lmem) ?goal] ] =>
    idtac "Ret v"; (* TODO: try Monad.bind_ret*? *)
    setoid_rewrite interp_st_Ret
  | [ |- context[ eutt eq (interp_st ?R ?t (ret ?v) ?lmem) ?goal ] ] =>
    idtac "ret v"; (* TODO: try Monad.bind_ret*? *)
    setoid_rewrite interp_st_ret
  | [ |- context[eutt eq (ret ?v) ?goal] ] =>
    idtac "pure value reflexivity";
    reflexivity
  | [ |- context[ eutt eq (Ret ?v) ?goal] ] =>
    idtac "pure value reflexivity";
    reflexivity
  | [ |- context[ eutt eq (interp_st _ _ (newSTRef _ _ ) _ ) ] ] =>
    idtac "newSTRef"; simp_interp_fun
  | [ |- context[ eutt eq (interp_st _ _ (readSTRef _ ) _ ) _ ] ] =>
    idtac "readSTRef"; simp_interp_fun
  | [ |- context[ eutt eq (interp_st _ _ (writeSTRef _ _ ) _ ) _ ] ] =>
    idtac "writeSTRef"; simp_interp_fun
  | [ |- context[ eutt eq (interp_st _ _ (newArray _ _ _ _ ) _ ) _ ] ] =>
    idtac "newArray"; simp_interp_fun
  | [ |- context[ eutt eq (interp_st _ _ (newListArray _ _ _ _ ) _ ) _ ] ] =>
    idtac "newListArray"; simp_interp_fun
  | [ |- context[ eutt eq (interp_st _ _ (readArray _ _ ) _ ) _ ] ] =>
    idtac "readArray"; simp_interp_fun
  | [ |- context[ eutt eq (interp_st _ _ (writeArray _ _ _ ) _ ) _ ] ] =>
    idtac "writeArray"; simp_interp_fun
  | [ |- context[ eutt eq (interp_st _ _ (getElems _) _ ) _ ] ] =>
    idtac "getElems"; simp_interp_fun
  end.

Ltac stforward_refine := stforward_inner simp_interp_leaf_refl.

Ltac stforward := stforward_inner simp_interp_leaf.
