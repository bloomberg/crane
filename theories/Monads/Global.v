(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Global mutable state: references and arrays whose values are typed by
    an index.  A program triggers [Event T V] events; a reference or array
    made at index [idx] holds values of type [V idx].  [run] interprets the
    program over a heterogeneous map from (location, index) keys to values;
    extraction maps references and arrays to the C++ types of ST's
    (theories/Monads/ST.v) and every operation to a direct C++ access, so
    the events disappear.  For extraction, give [V] as a notation or a
    section [Let], not a global definition, so that [V idx] reduces to the
    element type where Crane reads it. *)

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

(** How references are represented over a location type [T]: the model
    builds a reference from a location and reads the location back. *)
Class RefClass (T : Type) : Type :=
  {
    ref : forall A : Type, Type;
    make_ref : forall A : Type, T -> ref A;
    ref_index : forall A : Type, ref A -> T;
  }.

Section NatRefDefs.

  Variable (T : Type).

  (** A reference located at a natural number; [A] is a phantom type. *)
  Variant NatRef : Type -> Type :=
  | MkNatRef (A : Type) (idx : nat) : NatRef A.

  (** The location of a [NatRef]. *)
  Definition nat_ref_index (A : Type) (ref : NatRef A) : nat :=
   match ref with
   | MkNatRef _ idx => idx
   end.


End NatRefDefs.

(** References located at natural numbers. *)
#[global] Instance nat_ref_class : RefClass nat :=
  {| ref := NatRef;
    make_ref := MkNatRef ;
    ref_index := nat_ref_index |}.

Section ArrayDefs.

  Variable (T : Type).

  (** An array is the location of its first element and its size: element
      [i] lives at location [suc] applied [i] times to [base].  [A] is a
      phantom type. *)
  Variant array (A : Type) : Type := MkArray (base : T) (size : nat).

End ArrayDefs.

Arguments MkArray {T A} base size.

Section EventDefine.
  Variable (T : Type).
  Context `{RefClass T}.

(** The global-state effect: a reference made at index [idx] holds values
    of type [V idx]. *)
Variant Event (V : T -> Type) : Type -> Type :=
  | NewRef (idx : T) (v : V idx) : Event V (ref (V idx))
  | ReadRef (idx : T) : ref (V idx) -> Event V (V idx)
  | WriteRef (idx : T) : ref (V idx) -> (V idx) -> Event V unit
  | NewArray (idx : T) (n : nat) (def : V idx) : Event V (array T (V idx))
  | ArrayOfList (idx : T) (elems : list (V idx)) : Event V (array T (V idx))
  | ReadArray (idx : T) : array T (V idx) -> nat -> Event V (V idx)
  | WriteArray (idx : T) : array T (V idx) -> nat -> V idx -> Event V unit
  | ArrayToList (idx : T) : array T (V idx) -> Event V (list (V idx))
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


  (** A fresh reference at index [idx] holding [v].  The index is explicit
      because it cannot be inferred from [v]'s type. *)
  Definition new_ref (idx : T) (v : (V idx)) : itree E (ref (V idx)) :=
    trigger (NewRef T V idx v).

  (** The value [ref] holds. *)
  Definition read_ref {idx : T} (ref : ref (V idx)) : itree E (V idx) :=
    trigger (ReadRef T V idx ref).

  (** Overwrite the value [ref] holds. *)
  Definition write_ref {idx : T} (ref : ref (V idx)) (a : (V idx)) : itree E unit :=
    trigger (WriteRef T V idx ref a).

  (** A fresh array of [n] elements at index [idx], each [def], indexed
      from [0]. *)
  Definition new_array (idx : T) (n : nat) (def : V idx) : itree E (array T (V idx)) :=
    trigger (NewArray T V idx n def).

  (** A fresh array at index [idx] holding [elems] in order. *)
  Definition array_of_list (idx : T) (elems : list (V idx)) : itree E (array T (V idx)) :=
    trigger (ArrayOfList T V idx elems).

  (** Element [i] of [arr]; out of range fails. *)
  Definition read_array {idx : T} (arr : array T (V idx)) (i : nat) : itree E (V idx) :=
    trigger (ReadArray T V idx arr i).

  (** Overwrite element [i] of [arr]; out of range fails. *)
  Definition write_array {idx : T} (arr : array T (V idx)) (i : nat) (v : V idx)
    : itree E unit :=
    trigger (WriteArray T V idx arr i v).

  (** The elements of [arr], in order. *)
  Definition array_to_list {idx : T} (arr : array T (V idx)) : itree E (list (V idx)) :=
    trigger (ArrayToList T V idx arr).

  (** Exchange the elements at positions [i] and [j] of [arr]. *)
  Definition swap_array {idx : T} (arr : array T (V idx)) (i j : nat) : itree E unit :=
    vi <- read_array arr i;;
    vj <- read_array arr j;;
    write_array arr i vj;;
    write_array arr j vi.


  (** A store key: a location paired with the index typing its value. *)
  Definition pkey (J K : Type) := (J * K)%type.
  (** The type of the value stored at a key: [V] of its index. *)
  Definition pkey_type {J K} (V : K -> Type) (pk : pkey J K) := V (snd pk).
  (** Keys whose locations are of type [T]. *)
  Definition idx_key := pkey T.
  (** The type of the value stored at an [idx_key]. *)
  Definition idx_key_type {K} (V : K -> Type) (ik : idx_key K) := V (snd ik).

  Context {M : Type}.
  Context `{HMap (idx_key T) (idx_key_type V) M}.
  Context `{Foldable M (sigT (idx_key_type V))}.

  (** The location a new reference or array starts at: one past the
      largest location in use. *)
  Definition fresh (mem : M) : T :=
    suc (fold (fun '(existT _ (n, _) _) (acc : T) => max n acc) zero mem).

  (** The location of element [i] of an array starting at [base]. *)
  Fixpoint shift (base : T) (i : nat) : T :=
    match i with
    | O => base
    | S i' => suc (shift base i')
    end.

  (** [n] cells from [key] on, at index [idx], each holding [v]. *)
  Fixpoint fill (idx : T) (v : V idx) (key : T) (n : nat) (mem : M) : M :=
    match n with
    | O => mem
    | S n' => fill idx v (suc key) n' (add (key, idx) v mem)
    end.

  (** The cells from [key] on, at index [idx], holding [xs]. *)
  Fixpoint fill_list (idx : T) (key : T) (xs : list (V idx)) (mem : M) : M :=
    match xs with
    | nil => mem
    | x :: xs' => fill_list idx (suc key) xs' (add (key, idx) x mem)
    end.

  (** The cells [shift base k] at index [idx], for each [k] of [ks]. *)
  Fixpoint read_cells (idx base : T) (ks : list nat) (mem : M) : option (list (V idx)) :=
    match ks with
    | nil => Some nil
    | k :: ks' =>
      match lookup (shift base k, idx) mem, read_cells idx base ks' mem with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
    end.

  (** The model: a new reference or array takes the locations from [fresh]
      on; a read of a missing key, or an array index out of range, fails
      with [Err]. *)
  Definition handle `{EqDec T eq}
    : forall (A : Type), Event T V A -> Monads.stateT M (itree E) A :=
    fun _ e mem =>
    match e with
    | NewRef _ _ idx v =>
        let n := fresh mem
        in Ret (add (n, idx) v mem, make_ref (V idx) n)
    | ReadRef _ _ idx s =>
        match lookup (ref_index (V idx) s, idx) mem with
        | Some v => Ret (mem, v)
        | None => failwith "Lookup failed!"
        end
    | WriteRef _ _ idx s v => Ret (add (ref_index (V idx) s, idx) v mem, tt)
    | NewArray _ _ idx n def =>
        let b := fresh mem in Ret (fill idx def b n mem, MkArray b n)
    | ArrayOfList _ _ idx elems =>
        let b := fresh mem in
        Ret (fill_list idx b elems mem, MkArray b (List.length elems))
    | ReadArray _ _ idx a i =>
        let '(MkArray b n) := a in
        if Nat.ltb i n then
          match lookup (shift b i, idx) mem with
          | Some v => Ret (mem, v)
          | None => failwith "read_array: no such cell"
          end
        else failwith "read_array: index out of range"
    | WriteArray _ _ idx a i v =>
        let '(MkArray b n) := a in
        if Nat.ltb i n then Ret (add (shift b i, idx) v mem, tt)
        else failwith "write_array: index out of range"
    | ArrayToList _ _ idx a =>
        let '(MkArray b n) := a in
        match read_cells idx b (seq 0 n) mem with
        | Some vs => Ret (mem, vs)
        | None => failwith "array_to_list: no such cell"
        end
    end.


  (** [handle] on global-state events, the other events passed through. *)
  Definition handle_leave_rest
    (A : Type) (e : (Event T V +' E) A)
    : Monads.stateT M (itree (E)) A :=
    match e with
    | inl1 e0 => handle A e0
    | inr1 e0 => fun st : M => r <- trigger e0;; Ret (st, r)
    end.

  (** The default store: an association list keyed by index. *)
  #[global] Instance hmap_from_idx :
    HMap T V (halist T V) := @HMap_halist T V eq_equivalence _.

  (** The association-list store satisfies the [HMap] laws. *)
  #[global] Instance map_idx_correct :
    HMapOk hmap_from_idx := hmap_ok_halist T V.

  (** Interpret the global-state events of a tree into a state monad over
      the store. *)
  Definition interp
    : itree (Event T V +' E) ~> Monads.stateT M (itree (E)) :=
    interp_state handle_leave_rest.

End Construction.


(** Run a program from the empty store, returning the final store and the
    result. *)
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
Crane Extraction Implicit new_array [idx].
Crane Extraction Implicit array_of_list [idx].
Crane Extraction Implicit read_array [idx].
Crane Extraction Implicit write_array [idx].
Crane Extraction Implicit array_to_list [idx].
Crane Extraction Implicit swap_array [idx].

(** A reference is a mutable handle passed by const reference; copying it
    shares the cell. *)
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

(** [new_ref] allocates the cell with [std::make_shared]. *)
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

(** [read_ref] dereferences the handle. *)
#[global] Instance read_ref_mapping : OperationMapping (Ref (@read_ref)) :=
  {| operation_headers := [];
     operation_cpp := Expr "*%arg(ref)";
     operation_contract :=
       PureOperation
         [{| argument_name := "ref"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "ref"; path_components := ["contents"] |}] |}%pstring.

(** [write_ref] assigns through the handle. *)
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

From Crane Require Import Mapping.Cpp.
Import Crane.Cpp.

(** An array is ST's: a [std::shared_ptr<crane::array_storage<A>>]
    (theories/cpp/crane_st.h), a mutable handle passed by const reference.
    Its read view is [std::span<const A>] and its writable view
    [std::span<A>], both borrow-only: a generated function that only reads
    an array takes the read view, one that writes it the writable view. *)
#[global] Instance array_mapping (T : Type) (A : Type) : TypeMapping (@array T A) :=
  {| type_headers := ["crane_st.h"; "memory"];
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
         {| view_headers := ["span"; "utility"];
            view_cpp :=
              Crane.Cpp.Apply "std::span"
                [Crane.Cpp.TypeArg (Crane.Cpp.Const (Crane.Cpp.StoredComponent "contents"))];
            view_from_canonical := "std::span{std::as_const(*%value)}";
            view_escape := BorrowOnly |}
         {| view_headers := ["span"];
            view_cpp :=
              Crane.Cpp.Apply "std::span"
                [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")];
            view_from_canonical := "std::span{*%value}";
            view_escape := BorrowOnly |}
         "std::span<const %stored(contents)>{%view}";
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}%pstring.

(** [new_array] allocates [n] copies of [def] in one [array_storage]. *)
#[global] Instance new_array_mapping : OperationMapping (Ref (@new_array)) :=
  {| operation_headers := ["crane_st.h"; "memory"; "cstddef"];
     operation_cpp :=
       Structured (Call "std::make_shared" [Apply "crane::array_storage" [TypeArg (StoredComponent "contents")]] [to_size (Arg "n"); (Arg "def")]);
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "def"; argument_use := Take |}]
         (ReturnFreshIdentity
            [{| initial_component := "contents";
                initial_source_argument := Some "def";
                initial_multiplicity := InitialiseMany |}])
         [] |}%pstring.

(** [array_of_list] copies the list into a fresh [array_storage]. *)
#[global] Instance array_of_list_mapping : OperationMapping (Ref (@array_of_list)) :=
  {| operation_headers := ["crane_st.h"];
     operation_cpp :=
       Structured (Call "crane::st::new_list_array" [StoredComponent "contents"] [(Arg "elems")]);
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "elems"; argument_use := Read |}]
         (ReturnFreshIdentity
            [{| initial_component := "contents";
                initial_source_argument := Some "elems";
                initial_multiplicity := InitialiseMany |}])
         [] |}%pstring.

(** [read_array] is an unchecked index into the read view. *)
#[global] Instance read_array_mapping : OperationMapping (Ref (@read_array)) :=
  {| operation_headers := ["span"];
     operation_cpp := Structured (Index (Arg "arr") (Arg "i"));
     operation_contract :=
       PureOperation
         [{| argument_name := "arr"; argument_use := Read |};
          {| argument_name := "i"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "arr"; path_components := ["contents"] |}] |}%pstring.

(** [write_array] assigns through the writable view; the storage does not
    move, so only borrows of the old element are invalidated. *)
#[global] Instance write_array_mapping : OperationMapping (Ref (@write_array)) :=
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

(** [array_to_list] builds a fresh list of the elements. *)
#[global] Instance array_to_list_mapping : OperationMapping (Ref (@array_to_list)) :=
  {| operation_headers := ["crane_st.h"];
     operation_cpp := Structured (Call "crane::st::elems" [Apply "List" [TypeArg (StoredComponent "contents")]] [(Arg "arr")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "arr"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "arr"; path_components := ["contents"] |}] |}%pstring.

(** [swap_array] is [std::swap] of two elements in place. *)
#[global] Instance swap_array_mapping : OperationMapping (Ref (@swap_array)) :=
  {| operation_headers := ["span"; "utility"];
     operation_cpp := Structured (Call "std::swap" [] [(Index (Arg "arr") (Arg "i")); (Index (Arg "arr") (Arg "j"))]);
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "arr"; argument_use := Write |};
          {| argument_name := "i"; argument_use := Read |};
          {| argument_name := "j"; argument_use := Read |}]
         ReturnValue
         [WritesComponent {| path_argument := "arr"; path_components := ["contents"] |} None;
          InvalidatesElementBorrows {| path_argument := "arr"; path_components := ["contents"] |}] |}%pstring.
