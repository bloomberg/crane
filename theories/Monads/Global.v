(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

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
  Monads.ITree
  Monads.Error
  Monads.Indices
  Utils.HAList
  Utils.HMap
.


(* Global Ref Class*)

Class RefClass (T : Type) : Type :=
  {
    ref : forall A : Type, Type;
    make_ref : forall A : Type, T -> ref A;
    ref_index : forall A : Type, ref A -> T;
  }.


(* GlobalRef Event *)

Section NatRefDefs.

  Variable (T : Type).
  

  Variant NatRef : Type -> Type :=
  | MkNatRef (A : Type) (idx : nat) : NatRef A.

  
  Definition nat_ref_index (A : Type) (ref : NatRef A) : nat :=
   match ref with
   | MkNatRef _ idx => idx
   end. 


End NatRefDefs.

#[global] Instance nat_ref_class : RefClass nat :=
  {| ref := NatRef;
    make_ref := MkNatRef ;
    ref_index := nat_ref_index |}.

Section EventDefine.
  Variable (T : Type).
  Context `{RefClass T}. 

Variant Event (V : T -> Type) : Type -> Type :=
  | NewRef (idx : T) (v : V idx) : Event V (ref (V idx))
  | ReadRef (idx : T) : ref (V idx) -> Event V (V idx)
  | WriteRef (idx : T) : ref (V idx) -> (V idx) -> Event V unit
.

End EventDefine.

Section Construction.

  Context {E : Type -> Type}.
  Context {T : Type}.
  Context (ltu : T -> T -> Prop).
  Context `{Ix_Correct T ltu}.
  Context `{RefClass T}.
  Context {V : T -> Type}.
  Context `{Event T V -< E}. 
  Context `{exceptE Err -< E}.


  (* NOTE: explicit index here because we cannot infer it automatically, yet. *)
  Definition new_ref (idx : T) (v : (V idx)) : itree E (ref (V idx)) :=
    trigger (NewRef T V idx v).

  Definition read_ref {idx : T} (ref : ref (V idx)) : itree E (V idx) :=
    trigger (ReadRef T V idx ref).

  Definition write_ref {idx : T} (ref : ref (V idx)) (a : (V idx)) : itree E unit :=
    trigger (WriteRef T V idx ref a).


  (* key type definitions *)

  Definition pkey (J K : Type) := (J * K)%type.
  Definition pkey_type {J K} (V : K -> Type) (pk : pkey J K) := V (snd pk).
  Definition idx_key := pkey T. 
  Definition idx_key_type {K} (V : K -> Type) (ik : idx_key K) := V (snd ik).

  Context {M : Type}.
  Context `{HMap (idx_key T) (idx_key_type V) M}.
  Context `{Foldable M (sigT (idx_key_type V))}.

  (* Handler for GlobalRef *)
  
  Definition handle `{EqDec T eq} 
    : forall (A : Type), Event T V A -> Monads.stateT M (itree E) A :=
    fun _ e mem =>
    match e with
    | NewRef _ _ idx v =>
        let n := suc (fold (fun '(existT _ (n, _) _) (acc : T) => max n acc) zero mem)
        in Ret (add (n, idx) v mem, make_ref (V idx) n)
    | ReadRef _ _ idx s =>
        match lookup (ref_index (V idx) s, idx) mem with
        | Some v => Ret (mem, v)
        | None => failwith "Lookup failed!"
        end
    | WriteRef _ _ idx s v => Ret (add (ref_index (V idx) s, idx) v mem, tt)
    end.


  (* Interpretation in Rocq *)
    
  Definition handle_leave_rest
    (A : Type) (e : (Event T V +' E) A)
    : Monads.stateT M (itree (E)) A :=
    match e with
    | inl1 e0 => handle A e0
    | inr1 e0 => fun st : M => r <- trigger e0;; Ret (st, r)
    end.
  
  #[global] Instance hmap_from_idx :
    HMap T V (halist T V) := @HMap_halist T V eq_equivalence _.

  #[global] Instance map_idx_correct :
    HMapOk hmap_from_idx := HMapOk_halist T V.

  Definition interp
    : itree (Event T V +' E) ~> Monads.stateT M (itree (E)) :=
    interp_state handle_leave_rest.

End Construction.


Definition run {A : Type}
  {T : Type} {ltu : T -> T -> Prop}
  `{Ix T ltu}
  `{Ix_Correct T}
  `{EqDec T eq}
  `{RefClass T}
  {E : Type -> Type}
  {V : T -> Type} `{exceptE Err -< E}
  (t : itree ((Event T V) +' E) A)
  : itree E ((halist (idx_key T) (idx_key_type V)) * A) :=
  interp ltu _ t HMap.empty.

(* CPP Bindings *)

Crane Extract Skip Event.
Crane Extract Skip make_ref.
Crane Extract Skip ref_index.
(** A global reference is a [std::shared_ptr<A>], as an ST reference
    (theories/Monads/ST.v): a fresh cell per [new_ref]. *)

From Crane Require Import Mapping.Descriptor.
Import ListNotations.

Crane Extraction Implicit new_ref [idx].
Crane Extraction Implicit read_ref [idx].
Crane Extraction Implicit write_ref [idx].

#[global] Instance ref_mapping (T : Type) (H : RefClass T) (A : Type)
  : TypeMapping (@ref T H A) :=
  {| type_headers := ["memory"%pstring];
     type_cpp := Crane.Cpp.Apply "std::shared_ptr"
                   [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")];
     type_components :=
       [{| component_name := "contents"; component_type := KnownType A |}];
     type_copy := RetainIdentity;
     type_access := MutableHandle HandleByConstReference;
     type_views := NoViews (@ref T H A);
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}%pstring.

#[global] Instance new_ref_mapping : OperationMapping (Ref (@new_ref)) :=
  {| operation_headers := ["memory"];
     operation_cpp := Expr "std::make_shared<%stored(contents)>(%arg(v))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "v"; argument_use := Take |}]
         (ReturnFreshIdentity
            [{| initial_component := "contents";
                initial_source_argument := Some "v";
                initial_multiplicity := InitialiseOnce |}])
         [] |}%pstring.

#[global] Instance read_ref_mapping : OperationMapping (Ref (@read_ref)) :=
  {| operation_headers := [];
     operation_cpp := Expr "*%arg(ref)";
     operation_contract :=
       PureOperation
         [{| argument_name := "ref"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "ref"; path_components := ["contents"] |}] |}%pstring.

#[global] Instance write_ref_mapping : OperationMapping (Ref (@write_ref)) :=
  {| operation_headers := [];
     operation_cpp := Expr "*%arg(ref) = %arg(a)";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "ref"; argument_use := Write |};
          {| argument_name := "a"; argument_use := Take |}]
         ReturnValue
         [WritesComponent {| path_argument := "ref"; path_components := ["contents"] |} (Some "a");
          InvalidatesElementBorrows {| path_argument := "ref"; path_components := ["contents"] |}] |}%pstring.
