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
  PrimString
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

  (** Exchange the elements at positions [i] and [j] of [arr]. *)
  Definition swapArray {idx : T} (arr : STArray T S (V idx)) (i j : T)
    : itree E unit :=
    vi <- readArray (idx := idx) arr i;;
    vj <- readArray (idx := idx) arr j;;
    writeArray (idx := idx) arr i vj;;
    writeArray (idx := idx) arr j vi.


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
        | None => failwith "Lookup failed!"%pstring
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

(** Left fold of a monadic step over a list, threading an accumulator: the
    shape of an imperative [for] loop. Written as a [Fixpoint] because the
    equivalent [foldM] does not extract well. *)
Fixpoint for_each_with {E : Type -> Type} {A B : Type}
  (xs : list A) (v : B) (f : B -> A -> itree E B) : itree E B :=
  match xs with
  | nil => Ret v
  | h :: t => v' <- f v h;; for_each_with t v' f
  end.

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
(** References and arrays are typed mappings: a reference is a
    [std::shared_ptr<A>] and an array a
    [std::shared_ptr<crane::array_storage<A>>], each a mutable handle passed
    by const reference and owned by the shared pointer ([NativeRAII]).  An
    array has a read view, [std::span<const A>], and a writable view,
    [std::span<A>], both borrow-only (a copy of the elements would not be
    the same array): a generated function that only reads an array takes
    the read view, one that writes its elements the writable view, one that
    keeps it the handle by value, and one that replaces it the handle by
    reference.  [crane::array_storage] (theories/cpp/array_storage.h)
    stores one addressable element each, [bool] included, so the views are
    valid at every element type.  A reference has no view.
    Shared pointers do not collect cycles of references. *)

From Crane Require Import Mapping.Descriptor.

(** The index [idx] of an operation only selects the element type [V idx]:
    no operation reads it at run time. *)
Crane Extraction Implicit newSTRef [idx].
Crane Extraction Implicit readSTRef [idx].
Crane Extraction Implicit writeSTRef [idx].
Crane Extraction Implicit newArray [idx].
Crane Extraction Implicit newListArray [idx].
Crane Extraction Implicit readArray [idx].
Crane Extraction Implicit writeArray [idx].
Crane Extraction Implicit getElems [idx].

#[export] Instance st_ref_mapping (T : Type) (H : STRefClass T) (S A : Type)
  : TypeMapping (@STRef T H S A) :=
  {| type_headers := ["memory"%pstring];
     type_cpp := Crane.Cpp.Apply "std::shared_ptr"
                   [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")];
     type_components :=
       [{| component_name := "contents"; component_type := KnownType A |}];
     type_copy := RetainIdentity;
     type_access := MutableHandle HandleByConstReference;
     type_views :=
       ReadWriteViews
         {| view_headers := [];
            view_cpp := Crane.Cpp.Pointer (Crane.Cpp.Const (Crane.Cpp.StoredComponent "contents"));
            view_from_canonical := "%value.get()";
            view_escape := BorrowOnly |}
         {| view_headers := [];
            view_cpp := Crane.Cpp.Pointer (Crane.Cpp.StoredComponent "contents");
            view_from_canonical := "%value.get()";
            view_escape := BorrowOnly |}
         "%view";
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}%pstring.

(** A reference used only through its views where it is created lives in
    a local: [A x = v;], its views [&x]. *)
#[export] Instance st_ref_local (T : Type) (H : STRefClass T) (S A : Type)
  : LocalStorage (@STRef T H S A) :=
  {| local_view := "&%value"; local_tag := tt |}%pstring.

#[export] Instance new_st_ref_mapping : OperationMapping (Ref (@newSTRef)) :=
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

#[export] Instance read_st_ref_mapping : OperationMapping (Ref (@readSTRef)) :=
  {| operation_headers := [];
     operation_cpp := Expr "*%arg(ref)";
     operation_contract :=
       PureOperation
         [{| argument_name := "ref"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "ref"; path_components := ["contents"] |}] |}%pstring.

#[export] Instance write_st_ref_mapping : OperationMapping (Ref (@writeSTRef)) :=
  {| operation_headers := [];
     operation_cpp := Expr "*%arg(ref) = %arg(a)";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "ref"; argument_use := Write |};
          {| argument_name := "a"; argument_use := Take |}]
         ReturnValue
         [WritesComponent {| path_argument := "ref"; path_components := ["contents"] |} (Some "a");
          InvalidatesElementBorrows {| path_argument := "ref"; path_components := ["contents"] |}] |}%pstring.

#[export] Instance st_array_mapping (T S A : Type) : TypeMapping (STArray T S A) :=
  {| type_headers := ["array_storage.h"; "memory"];
     type_cpp :=
       Crane.Cpp.Apply "std::shared_ptr"
         [Crane.Cpp.TypeArg
            (Crane.Cpp.Apply "crane::array_storage"
               [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")])];
     type_components :=
       [{| component_name := "contents"; component_type := KnownType A |}];
     type_copy := RetainIdentity;
     type_access := MutableHandle HandleByConstReference;
     type_views :=
       ReadWriteViews
         {| view_headers := ["span"];
            view_cpp :=
              Crane.Cpp.Apply "std::span"
                [Crane.Cpp.TypeArg (Crane.Cpp.Const (Crane.Cpp.StoredComponent "contents"))];
            view_from_canonical := "std::span<const %stored(contents)>{*%value}";
            view_escape := BorrowOnly |}
         {| view_headers := ["span"];
            view_cpp :=
              Crane.Cpp.Apply "std::span"
                [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")];
            view_from_canonical := "std::span<%stored(contents)>{*%value}";
            view_escape := BorrowOnly |}
         "std::span<const %stored(contents)>{%view}";
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}%pstring.

#[export] Instance new_array_mapping : OperationMapping (Ref (@newArray)) :=
  {| operation_headers := ["crane_st.h"; "memory"];
     operation_cpp :=
       Expr "std::make_shared<crane::array_storage<%stored(contents)>>(crane::st::extent(%arg(lo), %arg(hi)), %arg(def))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "lo"; argument_use := Read |};
          {| argument_name := "hi"; argument_use := Read |};
          {| argument_name := "def"; argument_use := Take |}]
         (ReturnFreshIdentity
            [{| initial_component := "contents";
                initial_source_argument := Some "def";
                initial_multiplicity := InitialiseMany |}])
         [] |}%pstring.

#[export] Instance new_list_array_mapping : OperationMapping (Ref (@newListArray)) :=
  {| operation_headers := ["crane_st.h"];
     operation_cpp :=
       Expr "crane::st::new_list_array<%stored(contents)>(crane::st::extent(%arg(lo), %arg(hi)), %arg(elems))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "lo"; argument_use := Read |};
          {| argument_name := "hi"; argument_use := Read |};
          {| argument_name := "elems"; argument_use := Read |}]
         (ReturnFreshIdentity
            [{| initial_component := "contents";
                initial_source_argument := Some "elems";
                initial_multiplicity := InitialiseMany |}])
         [] |}%pstring.

(** [Read] gives the template the read view, [std::span<const A>]. *)
#[export] Instance read_array_mapping : OperationMapping (Ref (@readArray)) :=
  {| operation_headers := ["span"];
     operation_cpp := Expr "%arg(arr)[%arg(i)]";
     operation_contract :=
       PureOperation
         [{| argument_name := "arr"; argument_use := Read |};
          {| argument_name := "i"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "arr"; path_components := ["contents"] |}] |}%pstring.

(** [Write] gives the template the writable view, [std::span<A>].  Writing
    an element does not reallocate the storage: it invalidates borrows of
    the old element, not views of the array. *)
#[export] Instance write_array_mapping : OperationMapping (Ref (@writeArray)) :=
  {| operation_headers := ["span"];
     operation_cpp := Expr "%arg(arr)[%arg(i)] = %arg(v)";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "arr"; argument_use := Write |};
          {| argument_name := "i"; argument_use := Read |};
          {| argument_name := "v"; argument_use := Take |}]
         ReturnValue
         [WritesComponent {| path_argument := "arr"; path_components := ["contents"] |} (Some "v");
          InvalidatesElementBorrows {| path_argument := "arr"; path_components := ["contents"] |}] |}%pstring.

#[export] Instance get_elems_mapping : OperationMapping (Ref (@getElems)) :=
  {| operation_headers := ["crane_st.h"];
     operation_cpp := Expr "crane::st::elems<List<%stored(contents)>>(%arg(arr))";
     operation_contract :=
       PureOperation
         [{| argument_name := "arr"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "arr"; path_components := ["contents"] |}] |}%pstring.

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
Crane Extract Skip callE.


