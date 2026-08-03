(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Peano_dec
  Classes.EquivDec
  Init.Peano
  List
  Morphisms
  RelationClasses
  Relation_Definitions
  Setoid
  Strings.String
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
  Monads.ITree
  Monads.Error
  Monads.Indices
  Utils.HAList
  Utils.HMap
.


(* Global Ref Class*)

Class GlobRefClass (T : Type) : Type :=
  {
    GlobRef : forall A : Type, Type;
    mkGlobRef : forall A : Type, T -> GlobRef A;
    GlobRefToIx : forall A : Type, GlobRef A -> T;
  }.


(* GlobalRef Event *)

Section GlobRefNatDefs.

  Variable (T : Type).
  

  Variant GlobRefNat : Type -> Type :=
  | MkGlobRef (A : Type) (idx : nat) : GlobRefNat A.

  
  Definition GlobRefToIxNat (A : Type) (ref : GlobRefNat A) : nat :=
   match ref with
   | MkGlobRef _ idx => idx
   end. 


End GlobRefNatDefs.

#[export] Instance nat_ix_globref : GlobRefClass nat :=
  {| GlobRef := GlobRefNat;
    mkGlobRef := MkGlobRef ;
    GlobRefToIx := GlobRefToIxNat |}.

Section GlobEventDefine.
  Variable (T : Type).
  Context `{GlobRefClass T}. 

Variant GlobEvent (V : T -> Type) : Type -> Type :=
  | NewGlobRef (idx : T) (v : V idx) : GlobEvent V (GlobRef (V idx))
  | RebuildGlobRef (idx : T) : GlobEvent V (GlobRef (V idx))
  | ReadGlobRef (idx : T) : GlobRef (V idx) -> GlobEvent V (V idx)
  | WriteGlobRef (idx : T) : GlobRef (V idx) -> (V idx) -> GlobEvent V unit
.

End GlobEventDefine.

Section Construction.

  Context {E : Type -> Type}.
  Context {T : Type}.
  Context (ltu : T -> T -> Prop).
  Context `{Ix_Correct T ltu}.
  Context `{GlobRefClass T}.
  Context {V : T -> Type}.
  Context `{GlobEvent T V -< E}. 
  Context `{exceptE Err -< E}.


  (* NOTE: explicit index here because we cannot infer it automatically, yet. *)
  Definition newGlobRef (idx : T) (v : (V idx)) : itree E (GlobRef (V idx)) :=
    trigger (NewGlobRef T V idx v).

  Definition rebuildGlobRef (idx : T) : itree E (GlobRef (V idx)) :=
    trigger (RebuildGlobRef T V idx).

  Definition readGlobRef {idx : T} (ref : GlobRef (V idx)) : itree E (V idx) :=
    trigger (ReadGlobRef T V idx ref).

  Definition writeGlobRef {idx : T} (ref : GlobRef (V idx)) (a : (V idx)) : itree E unit :=
    trigger (WriteGlobRef T V idx ref a).


  (* key type definitions *)

  Definition pkey (J K : Type) := (J * K)%type.
  Definition pkey_type {J K} (V : K -> Type) (pk : pkey J K) := V (snd pk).
  Definition idx_key := pkey T. 
  Definition idx_key_type {K} (V : K -> Type) (ik : idx_key K) := V (snd ik).

  Context {M : Type}.
  Context `{HMap (idx_key T) (idx_key_type V) M}.
  Context `{Foldable M (sigT (idx_key_type V))}.

  (* Handler for GlobalRef *)
  
  Definition handle_GlobEvent `{EqDec T eq} 
    : forall (A : Type), GlobEvent T V A -> Monads.stateT M (itree E) A :=
    fun _ e mem =>
    match e with
    | NewGlobRef _ _ idx v =>
        let n := suc (fold (fun '(existT _ (n, _) _) (acc : T) => max n acc) zero mem)
        in Ret (add (n, idx) v mem, mkGlobRef (V idx) n)
    | RebuildGlobRef _ _ idx =>
        let n := suc (fold (fun '(existT _ (n, i) _) (acc : T) => if equiv_decb i idx then n else acc) zero mem)
        in Ret (mem, mkGlobRef (V idx) n)
    | ReadGlobRef _ _ idx s =>
        match lookup (GlobRefToIx (V idx) s, idx) mem with
        | Some v => Ret (mem, v)
        | None => failwith "Lookup failed!"
        end
    | WriteGlobRef _ _ idx s v => Ret (add (GlobRefToIx (V idx) s, idx) v mem, tt)
    end.


  (* Interpretation in Rocq *)
    
  Definition handle_GlobEvent_leave_rest
    (A : Type) (e : (GlobEvent T V +' E) A)
    : Monads.stateT M (itree (E)) A :=
    match e with
    | inl1 e0 => handle_GlobEvent A e0
    | inr1 e0 => fun st : M => r <- trigger e0;; Ret (st, r)
    end.
  
  #[export] Instance hmap_from_idx :
    HMap T V (halist T V) := @HMap_halist T V eq_equivalence _.

  #[export] Instance map_idx_correct :
    HMapOk hmap_from_idx := HMapOk_halist T V.

  Definition interp_glob
    : itree (GlobEvent T V +' E) ~> Monads.stateT M (itree (E)) :=
    interp_state handle_GlobEvent_leave_rest.

End Construction.


Definition runGlob {A : Type}
  {T : Type} {ltu : T -> T -> Prop}
  `{Ix T ltu}
  `{Ix_Correct T}
  `{EqDec T eq}
  `{GlobRefClass T}
  {E : Type -> Type}
  {V : T -> Type} `{exceptE Err -< E}
  (t : itree ((GlobEvent T V) +' E) A)
  : itree E ((halist (idx_key T) (idx_key_type V)) * A) :=
  interp_glob ltu _ t HMap.empty.

(* CPP Bindings *)

(* TODO: Dupes in here. *)
Crane Extract Skip Ix_Correct.
Crane Extract Skip CmpDec_Correct.
Crane Extract Skip GlobEvent.
Crane Extract Skip CmpDec.
Crane Extract Skip max.
Crane Extract Skip mkGlobRef.
Crane Extract Skip GlobRefToIx.
Crane Extract Inlined Constant GlobRef => "%t1".
Crane Extract Inlined Constant newGlobRef => "(_crane_globals[%a0] = %a1, %a0)" From "crane_globals.h".
Crane Extract Inlined Constant rebuildGlobRef => "%a0".
Crane Extract Inlined Constant readGlobRef => "std::any_cast<%t2>(_crane_globals.at(%a1))" From "crane_globals.h".
Crane Extract Inlined Constant writeGlobRef => "_crane_globals[%a1] = %a2" From "crane_globals.h".













