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

Import Monads.
Import ListNotations.
Import ProperNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.




Class STRefClass (T : Type) : Type :=
  {
    STRef : forall S A : Type, Type;
    mkSTRef : forall S A : Type, T -> STRef S A;
    STRefToIx : forall S A : Type, STRef S A -> T;
  }.


Section STRefNatDefs.

  Variable (T : Type).
  

  Variant STRefNat : Type -> Type -> Type :=
  | MkSTRef (S A : Type) (idx : nat) : STRefNat S A.

  
  Definition STRefToIxNat (S A : Type) (ref : STRefNat S A) : nat :=
   match ref with
   | MkSTRef _ _ idx => idx
   end. 

  Variant STArray (S A : Type) : Type :=
    | MkSTArray (base lo hi : T) : STArray S A.

  Definition stArrayBase {S A} (arr : STArray S A) : T :=
    match arr with MkSTArray _ _ base _ _ => base end.

  Definition stArrayBounds {S A} (arr : STArray S A) : T * T :=
    match arr with MkSTArray _ _ _ lo hi => (lo, hi) end.

End STRefNatDefs.

#[export] Instance nat_ix_stref : STRefClass nat :=
  {| STRef := STRefNat;
    mkSTRef := MkSTRef ;
    STRefToIx := STRefToIxNat |}.

Section STEventDefine.  
  Variable (T : Type).
  Context `{STRefClass T}.

  Variant STEvent (S : Type) (V : T -> Type) : Type -> Type :=
    | NewSTRef (idx : T) (v : V idx) : STEvent S V (STRef S (V idx))
    | ReadSTRef (idx : T) : STRef S (V idx) -> STEvent S V (V idx)
    | WriteSTRef (idx : T) : STRef S (V idx) -> (V idx) -> STEvent S V unit
    | NewArray (idx : T) (lo hi : T) (def : V idx) 
      : STEvent S V (STArray T S (V idx))
    | NewListArray (idx : T) (lo hi : T) (elems : list (V idx))
      : STEvent S V (STArray T S (V idx))
    | ReadArray (idx : T) : STArray T S (V idx) -> T -> STEvent S V (V idx)
    | WriteArray (idx : T) : STArray T S (V idx) -> T -> V idx -> STEvent S V unit
    | GetElems (idx : T) : STArray T S (V idx) -> STEvent S V (list (V idx))
  .

End STEventDefine.
  
  
Section Translation.

  Context {E : Type -> Type}.
  Context {T S : Type}.
  Context (ltu : T -> T -> Prop).
  Context `{Ix_Correct T ltu}.
  Context `{STRefClass T}.
  Context {V : T -> Type}.
  Context `{STEvent T S V -< E}. 
  Context `{exceptE Err -< E}.
  

  (* Smart constructors  *)

  (* NOTE: explicit index here because we cannot infer it automatically, yet. *)
  Definition newSTRef (idx : T) (v : (V idx)) : itree E (STRef S (V idx)) :=
    trigger (NewSTRef T S V idx v).

  Definition readSTRef {idx : T} (ref : STRef S (V idx)) : itree E (V idx) :=
    trigger (ReadSTRef T S V idx ref).

  Definition writeSTRef {idx : T} (ref : STRef S (V idx)) (a : (V idx)) : itree E unit :=
    trigger (WriteSTRef T S V idx ref a).

  Definition newArray (idx : T) (lo hi : T) (def : V idx)
    : itree E (STArray T S (V idx)) :=
    trigger (NewArray T S V idx lo hi def).

  (* NOTE: explicit index here because we cannot infer it. *)
  Definition newListArray (idx : T) (lo hi : T) (elems : list (V idx))
    : itree E (STArray T S (V idx)) :=
    trigger (NewListArray T S V idx lo hi elems).

  Definition readArray {idx : T} (arr : STArray T S (V idx)) (i : T)
    : itree E (V idx) :=
    trigger (ReadArray T S V idx arr i).

  Definition writeArray {idx : T} (arr : STArray T S (V idx)) (i : T) (v : V idx)
    : itree E unit :=
    trigger (WriteArray T S V idx arr i v).

  Definition getElems {idx : T} (arr : STArray T S (V idx))
    : itree E (list (V idx)) :=
    trigger (GetElems T S V idx arr).

  
  (* key type definitions *)

  Definition pkey (J K : Type) := (J * K)%type.
  Definition pkey_type {J K} (V : K -> Type) (pk : pkey J K) := V (snd pk).
  Definition idx_key := pkey T. 
  Definition idx_key_type {K} (V : K -> Type) (ik : idx_key K) := V (snd ik).


  Context {M : Type}.
  Context `{HMap (idx_key T) (idx_key_type V) M}.
  Context `{Foldable M (sigT (idx_key_type V))}.

  Fixpoint suc_n (n : nat) (t : T) : T :=
    match n with
    | O => t
    | Datatypes.S n' => suc (suc_n n' t)
    end.

  Definition arr_key (idx : T) (arr : STArray T S (V idx)) (i : T)
    : option T :=
    let 'MkSTArray _ _ _ base fb sb := arr in 
    match index fb sb i with
    | Some n => Some (suc_n n base)
    | None => None
    end.

  Definition arr_lookup (idx : T) (arr : STArray T S (V idx)) (i : T) (mem : M)
    : option (V idx) :=
    match arr_key idx arr i with
    | Some key => lookup (key, idx) mem
    | None => None
    end.

  (* The handler for STEvents itself *)
  Definition handle_STEvent `{EqDec T eq} 
    : forall (A : Type), STEvent T S V A -> stateT M (itree E) A :=
    fun _ e mem =>
    match e with
    | NewSTRef _ _ _ idx v =>
        let n := suc (fold (fun '(existT _ (n, _) _) (acc : T) => max n acc) zero mem)
        in Ret (add (n, idx) v mem, mkSTRef S (V idx) n)
    | ReadSTRef _ _ _ idx s =>
        match lookup (STRefToIx S (V idx) s, idx) mem with
        | Some v => Ret (mem, v)
        | None => failwith "Lookup failed!"
        end
    | WriteSTRef _ _ _ idx s v => Ret (add (STRefToIx S (V idx) s, idx) v mem, tt)
    | NewArray _ _ _ idx lo hi def =>
        let base := suc (fold (fun '(existT _ (n, _) _) (acc : T) => max n acc) zero mem) in
        let positions := range lo hi in
        let fix fill (ps : list T) (m : M) (key : T) {struct ps} : M * T :=
        match ps with
        | nil => (m, key) 
        | _ :: rest => fill rest (add (key, idx) def m) (suc key)
        end in
        let (mem', _ ) := fill positions mem base in
        Ret (mem', MkSTArray T S (V idx) base lo hi)
    | NewListArray _ _ _ idx lo hi elems =>
        let base := suc (fold (fun '(existT _ (n, _) _) (acc : T) => max n acc) zero mem) in
        let fix fill (es : list (V idx)) (m : M) (key : T) {struct es} : M * T :=
          match es with
          | nil => (m, key)
          | v :: rest => fill rest (add (key, idx) v m) (suc key)
          end in
        let '(mem', _) := fill elems mem base in
        Ret (mem', MkSTArray T S (V idx) base lo hi)
    | ReadArray _ _ _ idx arr i =>
        match arr_lookup idx arr i mem with
        | Some v => Ret (mem, v)
        | None => failwith "Array read failed"
        end
    | WriteArray _ _ _ idx arr i v =>
      match arr_key idx arr i with
      | Some key => Ret (add (key, idx) v mem, tt)
      | None => failwith "Array index out of range"
      end
    | GetElems _ _ _ idx arr =>
        let '(fb,sb) := stArrayBounds T arr in
        let positions := range fb sb in
        let fix collect (ps : list T) : option (list (V idx)) :=
          match ps with
          | nil => Some nil
          | p :: rest =>
            match arr_lookup idx arr p mem with
            | Some v =>
              match collect rest with
              | Some elems => Some (v :: elems)
              | None => None
              end
            | None => None
            end
          end in
        match collect positions with
        | Some elems => Ret (mem, elems)
        | None => failwith "Array getElems failed"
        end
    end.

(* Interpretation in Rocq *)

  Definition handle_STEvent_leave_rest
    (A : Type) (e : (STEvent T S V +' E) A)
    : stateT M (itree (E)) A :=
    match e with
    | inl1 e0 => handle_STEvent A e0
    | inr1 e0 => fun st : M => r <- trigger e0;; Ret (st, r)
    end.
  
  #[export] Instance hmap_from_idx :
    HMap T V (halist T V) := @HMap_halist T V eq_equivalence _.

  #[export] Instance map_idx_correct :
    HMapOk hmap_from_idx := HMapOk_halist T V.

  Definition interp_st
    : itree (STEvent T S V +' E) ~> stateT M (itree (E)) :=
    interp_state handle_STEvent_leave_rest.

  
End Translation.

Definition runST {A : Type}
  {T S : Type} {ltu : T -> T -> Prop}
  `{Ix T ltu}
  `{Ix_Correct T}
  `{EqDec T eq}
  `{STRefClass T}
  {E : Type -> Type}
  {V : T -> Type} `{exceptE Err -< E}
  (f : forall (S : Type), itree ((STEvent T S V) +' E) A)
  : itree E A :=
  fmap snd (interp_st ltu _ (f unit) HMap.empty).

(* CPP Bindings *)

Crane Extraction Implicit newSTRef[1].
Crane Extract Skip Ix_Correct.
Crane Extract Skip CmpDec_Correct.
Crane Extract Skip STEvent.
Crane Extract Skip CmpDec.
Crane Extract Skip max.
Crane Extract Skip mkSTRef.
Crane Extract Skip STRefToIx.
(* NOTE: skipping STRefClass seems to drop too much typing information,
 and the value types within references are not inferred. *)
(* Crane Extract Skip STRefClass. *)
Crane Extract Inlined Constant STRef => "%t2".
Crane Extract Inlined Constant newSTRef => "%result = %a1".
Crane Extract Inlined Constant readSTRef => "%a1".
Crane Extract Inlined Constant writeSTRef => "%a1 = %a2".
(* array extraction *)

Crane Extract Inductive STArray => "std::vector<%t2> *" [ "" ].
Crane Extract Inlined Constant newArray =>
"%result = new std::remove_pointer_t<decltype(%result)>(%a2 - %a1 + 1, %a3)".
Crane Extract Inlined Constant readArray => "(*%a1)[%a2]".
Crane Extract Inlined Constant writeArray => "(*%a1)[%a2] = %a3".

Crane Extract Inlined Constant newListArray =>
  "%result = new std::remove_pointer_t<decltype(%result)>(%a2 - %a1 + 1); { auto _xs = %a3; for (size_t _i = 0; _i < %result->size(); _i++) { if (std::holds_alternative<typename std::remove_cvref_t<decltype(_xs)>::Cons>(_xs.v())) { auto& [_a, _l] = std::get<typename std::remove_cvref_t<decltype(_xs)>::Cons>(_xs.v_mut()); (*%result)[_i] = _a; if (_l) _xs = *_l; } } }".
Crane Extract Inlined Constant getElems =>
  "[&]() { using _E = typename std::remove_pointer_t<std::remove_cvref_t<decltype(%a1)>>::value_type; List<_E> _r = List<_E>::nil(); for (size_t _i = %a1->size(); _i > 0; _i--) { _r = List<_E>::cons((*%a1)[_i - 1], std::move(_r)); } return _r; }()".

(* Recursion is mapped to a while loop that models the stack explicitly. *)
(* NOTE: should this go in ITree base as part of the erased translation? *)
Crane Extract Skip Module Recursion.
Crane Extract Inlined Constant rec =>
        "[&]() { static std::vector<%t1> _stack;
                _stack.push_back(%a1);
                while (!_stack.empty()) {
                  %t1 _arg = _stack.back();
                  _stack.pop_back();
                  %a0(_arg);
        } } ();".

Crane Extract Inlined Constant call => "(_stack.push_back(%a0), std::monostate{})".


