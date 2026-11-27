(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Local mutable state: references and arrays in the [itree] of a program,
    run by [runST].

    A program is written against an abstract [STRefs], the type of
    references and the type of arrays and nothing more, and [runST] takes it
    polymorphic in them: [forall R : STRefs, itree (STEvent R V +' E) A].
    Inside the program a reference is of an abstract type, so the program
    cannot look into one, forge one, or return one from the run.  [runST]
    interprets the program with [model_refs], where a reference is a
    location in a store; extraction maps the reference and array types of
    every [STRefs] to C++, a [std::shared_ptr] and an [array_storage].

    Values of different types share the store through codes: [V c] is the
    type of the values stored at code [c], and a value of type [A] is stored
    at the code a [Code V A] instance gives it, so no operation takes a code
    argument.  [code_const] gives every type its code where all values have
    one type. *)

From Stdlib Require Import
  Arith.PeanoNat
  Classes.EquivDec
  List
  PrimString
.

From ITree Require Import
  Events.Exception
  Events.State
  ITree
.

From Crane Require Import
  Extraction
  Monads.Error
  Monads.ITree
  Utils.HAList
  Utils.HMap
.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

(** The types a program sees: references and arrays holding values of a
    type. *)
Class STRefs : Type := {
  STRef : Type -> Type;
  STArray : Type -> Type
}.

(** [A] is stored at code [code], whose values [V code] are of type [A]. *)
Class Code (V : nat -> Type) (A : Type) : Type := {
  code : nat;
  code_ok : V code = A
}.
Arguments code V A {Code}.
Arguments code_ok V A {Code}.

#[export] Instance code_const (A : Type) : Code (fun _ : nat => A) A :=
  {| code := 0; code_ok := eq_refl |}.

Variant STEvent (R : STRefs) (V : nat -> Type) : Type -> Type :=
| NewSTRef (c : nat) (v : V c) : STEvent R V (@STRef R (V c))
| ReadSTRef (c : nat) (ref : @STRef R (V c)) : STEvent R V (V c)
| WriteSTRef (c : nat) (ref : @STRef R (V c)) (v : V c) : STEvent R V unit
| NewArray (c : nat) (n : nat) (def : V c) : STEvent R V (@STArray R (V c))
| NewListArray (c : nat) (elems : list (V c)) : STEvent R V (@STArray R (V c))
| ReadArray (c : nat) (arr : @STArray R (V c)) (i : nat) : STEvent R V (V c)
| WriteArray (c : nat) (arr : @STArray R (V c)) (i : nat) (v : V c) : STEvent R V unit
| GetElems (c : nat) (arr : @STArray R (V c)) : STEvent R V (list (V c)).

Section Operations.

  Context {R : STRefs} {V : nat -> Type} {E : Type -> Type} `{STEvent R V -< E}.

  (** Each operation stores [A] at [code V A], through [code_ok]. *)
  Definition newSTRef {A : Type} `{Code V A} (v : A) : itree E (STRef A) :=
    match code_ok V A in _ = X return X -> itree E (STRef X) with
    | eq_refl => fun v => trigger (NewSTRef R V (code V A) v)
    end v.

  Definition readSTRef {A : Type} `{Code V A} (ref : STRef A) : itree E A :=
    match code_ok V A in _ = X return STRef X -> itree E X with
    | eq_refl => fun ref => trigger (ReadSTRef R V (code V A) ref)
    end ref.

  Definition writeSTRef {A : Type} `{Code V A} (ref : STRef A) (a : A) : itree E unit :=
    match code_ok V A in _ = X return STRef X -> X -> itree E unit with
    | eq_refl => fun ref a => trigger (WriteSTRef R V (code V A) ref a)
    end ref a.

  (** An array of [n] elements, indexed from [0]. *)
  Definition newArray {A : Type} `{Code V A} (n : nat) (def : A) : itree E (STArray A) :=
    match code_ok V A in _ = X return X -> itree E (STArray X) with
    | eq_refl => fun def => trigger (NewArray R V (code V A) n def)
    end def.

  Definition newListArray {A : Type} `{Code V A} (elems : list A) : itree E (STArray A) :=
    match code_ok V A in _ = X return list X -> itree E (STArray X) with
    | eq_refl => fun elems => trigger (NewListArray R V (code V A) elems)
    end elems.

  Definition readArray {A : Type} `{Code V A} (arr : STArray A) (i : nat) : itree E A :=
    match code_ok V A in _ = X return STArray X -> itree E X with
    | eq_refl => fun arr => trigger (ReadArray R V (code V A) arr i)
    end arr.

  Definition writeArray {A : Type} `{Code V A} (arr : STArray A) (i : nat) (v : A)
    : itree E unit :=
    match code_ok V A in _ = X return STArray X -> X -> itree E unit with
    | eq_refl => fun arr v => trigger (WriteArray R V (code V A) arr i v)
    end arr v.

  Definition getElems {A : Type} `{Code V A} (arr : STArray A) : itree E (list A) :=
    match code_ok V A in _ = X return STArray X -> itree E (list X) with
    | eq_refl => fun arr => trigger (GetElems R V (code V A) arr)
    end arr.

  (** Exchange the elements at positions [i] and [j] of [arr]. *)
  Definition swapArray {A : Type} `{Code V A} (arr : STArray A) (i j : nat) : itree E unit :=
    vi <- readArray arr i;;
    vj <- readArray arr j;;
    writeArray arr i vj;;
    writeArray arr j vi.

End Operations.

(** Left fold of a monadic step over a list, threading an accumulator: the
    shape of an imperative [for] loop. Written as a [Fixpoint] because the
    equivalent [foldM] does not extract well. *)
Fixpoint for_each_with {E : Type -> Type} {A B : Type}
  (xs : list A) (v : B) (f : B -> A -> itree E B) : itree E B :=
  match xs with
  | nil => Ret v
  | h :: t => v' <- f v h;; for_each_with t v' f
  end.

(** * The model *)

(** An array is the location of its first element and its size. *)
Variant ArrLoc (A : Type) : Type := MkArrLoc (base size : nat).
Arguments MkArrLoc {A} base size.

(** A reference is a location; an array its first location and size. *)
Definition model_refs : STRefs := {| STRef := fun _ => nat; STArray := ArrLoc |}.

(** The store maps a location and a code to a value of the code's type. *)
Definition key_type (V : nat -> Type) (k : nat * nat) : Type := V (snd k).
Definition mem (V : nat -> Type) : Type := halist (nat * nat) (key_type V).

(** Decided by a transparent term, so that a lookup in a closed store
    computes. *)
Definition st_key_eq_dec (x y : nat * nat) : {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

#[export] Instance st_key_eqdec : EqDec (nat * nat) eq := st_key_eq_dec.

#[export] Instance st_hmap (V : nat -> Type) : HMap (nat * nat) (key_type V) (mem V) :=
  @HMap_halist (nat * nat) (key_type V) eq_equivalence st_key_eqdec.

#[export] Instance st_hmap_ok (V : nat -> Type) : HMapOk (st_hmap V) :=
  HMapOk_halist (nat * nat) (key_type V).

Section Model.

  Context {V : nat -> Type} {E : Type -> Type} `{exceptE Err -< E}.

  (** The location a new reference or array starts at: one past the largest
      location in use. *)
  Definition st_fresh (m : mem V) : nat :=
    S (fold_halist (nat * nat) (key_type V) (fun k _ acc => Nat.max (fst k) acc) 0 m).

  (** [n] cells from [key] on, each holding [v]. *)
  Fixpoint fill (c : nat) (v : V c) (key n : nat) (m : mem V) : mem V :=
    match n with
    | O => m
    | S n' => fill c v (S key) n' (add (key, c) v m)
    end.

  (** The cells from [key] on, holding [xs]. *)
  Fixpoint fill_list (c : nat) (key : nat) (xs : list (V c)) (m : mem V) : mem V :=
    match xs with
    | [] => m
    | x :: xs' => fill_list c (S key) xs' (add (key, c) x m)
    end.

  (** The cells [base + k] for each [k] of [ks]. *)
  Fixpoint read_cells (c base : nat) (ks : list nat) (m : mem V) : option (list (V c)) :=
    match ks with
    | [] => Some []
    | k :: ks' =>
      match lookup (base + k, c) m, read_cells c base ks' m with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
    end.

  Definition handle_STEvent : STEvent model_refs V ~> stateT (mem V) (itree E) :=
    fun _ e m =>
    match e with
    | NewSTRef _ _ c v => let l := st_fresh m in Ret (add (l, c) v m, l)
    | ReadSTRef _ _ c l =>
      match lookup (l, c) m with
      | Some v => Ret (m, v)
      | None => failwith "readSTRef: no such reference"%pstring
      end
    | WriteSTRef _ _ c l v => Ret (add (l, c) v m, tt)
    | NewArray _ _ c n def =>
      let b := st_fresh m in Ret (fill c def b n m, MkArrLoc b n)
    | NewListArray _ _ c elems =>
      let b := st_fresh m in Ret (fill_list c b elems m, MkArrLoc b (List.length elems))
    | ReadArray _ _ c a i =>
      let '(MkArrLoc b n) := a in
      if Nat.ltb i n then
        match lookup (b + i, c) m with
        | Some v => Ret (m, v)
        | None => failwith "readArray: no such cell"%pstring
        end
      else failwith "readArray: index out of range"%pstring
    | WriteArray _ _ c a i v =>
      let '(MkArrLoc b n) := a in
      if Nat.ltb i n then Ret (add (b + i, c) v m, tt)
      else failwith "writeArray: index out of range"%pstring
    | GetElems _ _ c a =>
      let '(MkArrLoc b n) := a in
      match read_cells c b (seq 0 n) m with
      | Some vs => Ret (m, vs)
      | None => failwith "getElems: no such cell"%pstring
      end
    end.

  Definition handle_STEvent_leave_rest : (STEvent model_refs V +' E) ~> stateT (mem V) (itree E) :=
    fun _ e m =>
    match e with
    | inl1 e0 => handle_STEvent _ e0 m
    | inr1 e0 => r <- trigger e0;; Ret (m, r)
    end.

  Definition interp_st : itree (STEvent model_refs V +' E) ~> stateT (mem V) (itree E) :=
    interp_state handle_STEvent_leave_rest.

End Model.

(** A program polymorphic in its references and arrays, run from the empty
    store. *)
Definition runST {V : nat -> Type} {E : Type -> Type} `{exceptE Err -< E} {A : Type}
  (f : forall R : STRefs, itree (STEvent R V +' E) A) : itree E A :=
  ITree.map snd (interp_st _ (f model_refs) (@empty _ _ _ (st_hmap V))).

(** * Extraction *)

(** The references and arrays the extracted program is written against:
    their types are mapped below, whatever [STRefs] they come from. *)
Axiom cpp_refs : STRefs.

(** Runs a program in C++: the extracted program performs its effects
    where it is written, so running it is calling it. *)
Axiom run_st : forall {V : nat -> Type} {A : Type},
  itree (STEvent cpp_refs V +' exceptE Err) A -> A.

Crane Extract Skip STEvent.
Crane Extract Skip code_ok.
Crane Extract Inlined Constant run_st => "%a0".
(** [STRefs] holds only types, so it is a one-constructor enum in C++. *)
Crane Extract Inlined Constant cpp_refs => "STRefs::BUILD_STREFS".

(** References and arrays are typed mappings: a reference is a
    [std::shared_ptr<A>] and an array a
    [std::shared_ptr<crane::array_storage<A>>], each a mutable handle passed
    by const reference and owned by the shared pointer ([NativeRAII]).  A
    reference has a read view, [const A*], and a writable view, [A*]; an
    array a read view, [std::span<const A>], and a writable view,
    [std::span<A>]; all borrow-only (a copy would not be the same reference
    or array): a generated function that only reads one takes the read
    view, one that writes it the writable view, one that keeps it the
    handle by value.  [crane::array_storage] (theories/cpp/crane_st.h)
    stores one addressable element each, [bool] included, so the views are
    valid at every element type.  Shared pointers do not collect cycles of
    references. *)

From Crane Require Import Mapping.Descriptor.

(** The [STRefs] a program is written against is a C++ value with nothing
    in it: the operations take no such argument. *)
Crane Extraction Implicit newSTRef [R].
Crane Extraction Implicit readSTRef [R].
Crane Extraction Implicit writeSTRef [R].
Crane Extraction Implicit newArray [R].
Crane Extraction Implicit newListArray [R].
Crane Extraction Implicit readArray [R].
Crane Extraction Implicit writeArray [R].
Crane Extraction Implicit getElems [R].

#[export] Instance st_ref_mapping (R : STRefs) (A : Type)
  : TypeMapping (@STRef R A) :=
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
#[export] Instance st_ref_local (R : STRefs) (A : Type)
  : LocalStorage (@STRef R A) :=
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

#[export] Instance st_array_mapping (R : STRefs) (A : Type) : TypeMapping (@STArray R A) :=
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

#[export] Instance new_array_mapping : OperationMapping (Ref (@newArray)) :=
  {| operation_headers := ["crane_st.h"; "memory"];
     operation_cpp :=
       Expr "std::make_shared<crane::array_storage<%stored(contents)>>(static_cast<std::size_t>(%arg(n)), %arg(def))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "def"; argument_use := Take |}]
         (ReturnFreshIdentity
            [{| initial_component := "contents";
                initial_source_argument := Some "def";
                initial_multiplicity := InitialiseMany |}])
         [] |}%pstring.

#[export] Instance new_list_array_mapping : OperationMapping (Ref (@newListArray)) :=
  {| operation_headers := ["crane_st.h"];
     operation_cpp :=
       Expr "crane::st::new_list_array<%stored(contents)>(%arg(elems))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "elems"; argument_use := Read |}]
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

Crane Extraction Implicit swapArray [R].

(** [Write] gives the template the writable view, [std::span<A>]. *)
#[export] Instance swap_array_mapping : OperationMapping (Ref (@swapArray)) :=
  {| operation_headers := ["span"; "utility"];
     operation_cpp := Expr "std::swap(%arg(arr)[%arg(i)], %arg(arr)[%arg(j)])";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "arr"; argument_use := Write |};
          {| argument_name := "i"; argument_use := Read |};
          {| argument_name := "j"; argument_use := Read |}]
         ReturnValue
         [WritesComponent {| path_argument := "arr"; path_components := ["contents"] |} None;
          InvalidatesElementBorrows {| path_argument := "arr"; path_components := ["contents"] |}] |}%pstring.
