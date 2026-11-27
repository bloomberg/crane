(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Local mutable state: references and arrays in the [itree] of a program,
    run by [run].

    A program is written against an abstract [Refs], the type of
    references and the type of arrays and nothing more, and [run] takes it
    polymorphic in them: [forall R : Refs, itree (Event R V +' E) A].
    Inside the program a reference is of an abstract type, so the program
    cannot look into one, forge one, or return one from the run.  [run]
    interprets the program with [model_refs], where a reference is a
    location in a store; extraction maps the reference and array types of
    every [Refs] to C++, a [std::shared_ptr] and an [array_storage].

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
Class Refs : Type := {
  ref : Type -> Type;
  array : Type -> Type
}.

(** [A] is stored at code [code], whose values [V code] are of type [A]. *)
Class Code (V : nat -> Type) (A : Type) : Type := {
  code : nat;
  code_ok : V code = A
}.
Arguments code V A {Code}.
Arguments code_ok V A {Code}.

#[global] Instance code_const (A : Type) : Code (fun _ : nat => A) A :=
  {| code := 0; code_ok := eq_refl |}.

Variant Event (R : Refs) (V : nat -> Type) : Type -> Type :=
| NewRef (c : nat) (v : V c) : Event R V (@ref R (V c))
| ReadRef (c : nat) (r : @ref R (V c)) : Event R V (V c)
| WriteRef (c : nat) (r : @ref R (V c)) (v : V c) : Event R V unit
| NewArray (c : nat) (n : nat) (def : V c) : Event R V (@array R (V c))
| ArrayOfList (c : nat) (elems : list (V c)) : Event R V (@array R (V c))
| ReadArray (c : nat) (arr : @array R (V c)) (i : nat) : Event R V (V c)
| WriteArray (c : nat) (arr : @array R (V c)) (i : nat) (v : V c) : Event R V unit
| ArrayToList (c : nat) (arr : @array R (V c)) : Event R V (list (V c)).

Section Operations.

  Context {R : Refs} {V : nat -> Type} {E : Type -> Type} `{Event R V -< E}.

  (** Each operation stores [A] at [code V A], through [code_ok]. *)
  Definition new_ref {A : Type} `{Code V A} (v : A) : itree E (ref A) :=
    match code_ok V A in _ = X return X -> itree E (ref X) with
    | eq_refl => fun v => trigger (NewRef R V (code V A) v)
    end v.

  Definition read_ref {A : Type} `{Code V A} (r : ref A) : itree E A :=
    match code_ok V A in _ = X return ref X -> itree E X with
    | eq_refl => fun r => trigger (ReadRef R V (code V A) r)
    end r.

  Definition write_ref {A : Type} `{Code V A} (r : ref A) (a : A) : itree E unit :=
    match code_ok V A in _ = X return ref X -> X -> itree E unit with
    | eq_refl => fun r a => trigger (WriteRef R V (code V A) r a)
    end r a.

  (** An array of [n] elements, indexed from [0]. *)
  Definition new_array {A : Type} `{Code V A} (n : nat) (def : A) : itree E (array A) :=
    match code_ok V A in _ = X return X -> itree E (array X) with
    | eq_refl => fun def => trigger (NewArray R V (code V A) n def)
    end def.

  Definition array_of_list {A : Type} `{Code V A} (elems : list A) : itree E (array A) :=
    match code_ok V A in _ = X return list X -> itree E (array X) with
    | eq_refl => fun elems => trigger (ArrayOfList R V (code V A) elems)
    end elems.

  Definition read_array {A : Type} `{Code V A} (arr : array A) (i : nat) : itree E A :=
    match code_ok V A in _ = X return array X -> itree E X with
    | eq_refl => fun arr => trigger (ReadArray R V (code V A) arr i)
    end arr.

  Definition write_array {A : Type} `{Code V A} (arr : array A) (i : nat) (v : A)
    : itree E unit :=
    match code_ok V A in _ = X return array X -> X -> itree E unit with
    | eq_refl => fun arr v => trigger (WriteArray R V (code V A) arr i v)
    end arr v.

  Definition array_to_list {A : Type} `{Code V A} (arr : array A) : itree E (list A) :=
    match code_ok V A in _ = X return array X -> itree E (list X) with
    | eq_refl => fun arr => trigger (ArrayToList R V (code V A) arr)
    end arr.

  (** Exchange the elements at positions [i] and [j] of [arr]. *)
  Definition swap_array {A : Type} `{Code V A} (arr : array A) (i j : nat) : itree E unit :=
    vi <- read_array arr i;;
    vj <- read_array arr j;;
    write_array arr i vj;;
    write_array arr j vi.

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
Variant ArrayLoc (A : Type) : Type := MkArrayLoc (base size : nat).
Arguments MkArrayLoc {A} base size.

(** A reference is a location; an array its first location and size. *)
Definition model_refs : Refs := {| ref := fun _ => nat; array := ArrayLoc |}.

(** The store maps a location and a code to a value of the code's type. *)
Definition key_type (V : nat -> Type) (k : nat * nat) : Type := V (snd k).
Definition mem (V : nat -> Type) : Type := halist (nat * nat) (key_type V).

(** Decided by a transparent term, so that a lookup in a closed store
    computes. *)
Definition key_eq_dec (x y : nat * nat) : {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

#[global] Instance key_eq_dec_instance : EqDec (nat * nat) eq := key_eq_dec.

#[global] Instance hmap (V : nat -> Type) : HMap (nat * nat) (key_type V) (mem V) :=
  @HMap_halist (nat * nat) (key_type V) eq_equivalence key_eq_dec_instance.

#[global] Instance hmap_ok (V : nat -> Type) : HMapOk (hmap V) :=
  HMapOk_halist (nat * nat) (key_type V).

Section Model.

  Context {V : nat -> Type} {E : Type -> Type} `{exceptE Err -< E}.

  (** The location a new reference or array starts at: one past the largest
      location in use. *)
  Definition fresh (m : mem V) : nat :=
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

  Definition handle : Event model_refs V ~> stateT (mem V) (itree E) :=
    fun _ e m =>
    match e with
    | NewRef _ _ c v => let l := fresh m in Ret (add (l, c) v m, l)
    | ReadRef _ _ c l =>
      match lookup (l, c) m with
      | Some v => Ret (m, v)
      | None => failwith "read_ref: no such reference"%pstring
      end
    | WriteRef _ _ c l v => Ret (add (l, c) v m, tt)
    | NewArray _ _ c n def =>
      let b := fresh m in Ret (fill c def b n m, MkArrayLoc b n)
    | ArrayOfList _ _ c elems =>
      let b := fresh m in Ret (fill_list c b elems m, MkArrayLoc b (List.length elems))
    | ReadArray _ _ c a i =>
      let '(MkArrayLoc b n) := a in
      if Nat.ltb i n then
        match lookup (b + i, c) m with
        | Some v => Ret (m, v)
        | None => failwith "read_array: no such cell"%pstring
        end
      else failwith "read_array: index out of range"%pstring
    | WriteArray _ _ c a i v =>
      let '(MkArrayLoc b n) := a in
      if Nat.ltb i n then Ret (add (b + i, c) v m, tt)
      else failwith "write_array: index out of range"%pstring
    | ArrayToList _ _ c a =>
      let '(MkArrayLoc b n) := a in
      match read_cells c b (seq 0 n) m with
      | Some vs => Ret (m, vs)
      | None => failwith "array_to_list: no such cell"%pstring
      end
    end.

  Definition handle_leave_rest : (Event model_refs V +' E) ~> stateT (mem V) (itree E) :=
    fun _ e m =>
    match e with
    | inl1 e0 => handle _ e0 m
    | inr1 e0 => r <- trigger e0;; Ret (m, r)
    end.

  Definition interp : itree (Event model_refs V +' E) ~> stateT (mem V) (itree E) :=
    interp_state handle_leave_rest.

End Model.

(** A program polymorphic in its references and arrays, run from the empty
    store. *)
Definition run {V : nat -> Type} {E : Type -> Type} `{exceptE Err -< E} {A : Type}
  (f : forall R : Refs, itree (Event R V +' E) A) : itree E A :=
  ITree.map snd (interp _ (f model_refs) (@empty _ _ _ (hmap V))).

(** * Extraction *)

(** The references and arrays the extracted program is written against:
    their types are mapped below, whatever [Refs] they come from. *)
Axiom cpp_refs : Refs.

(** Runs a program in C++: the extracted program performs its effects
    where it is written, so running it is calling it. *)
Axiom run_cpp : forall {V : nat -> Type} {A : Type},
  itree (Event cpp_refs V +' exceptE Err) A -> A.

Crane Extract Skip Event.
Crane Extract Skip code_ok.
Crane Extract Inlined Constant run_cpp => "%a0".
(** [Refs] holds only types, so it is a one-constructor enum in C++. *)
Crane Extract Inlined Constant cpp_refs => "Refs::BUILD_REFS".

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

From Crane Require Import Mapping.Descriptor Mapping.Cpp.
Import Crane.Cpp.

(** The [Refs] a program is written against is a C++ value with nothing
    in it: the operations take no such argument. *)
Crane Extraction Implicit new_ref [R].
Crane Extraction Implicit read_ref [R].
Crane Extraction Implicit write_ref [R].
Crane Extraction Implicit new_array [R].
Crane Extraction Implicit array_of_list [R].
Crane Extraction Implicit read_array [R].
Crane Extraction Implicit write_array [R].
Crane Extraction Implicit array_to_list [R].

#[global] Instance ref_mapping (R : Refs) (A : Type)
  : TypeMapping (@ref R A) :=
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
#[global] Instance ref_local (R : Refs) (A : Type)
  : LocalStorage (@ref R A) :=
  {| local_view := "&%value"; local_tag := tt |}%pstring.

#[global] Instance new_ref_mapping : OperationMapping (Ref (@new_ref)) :=
  {| operation_headers := ["memory"];
     operation_cpp := Structured (Call "std::make_shared" [StoredComponent "contents"] [(Arg "v")]);
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
     operation_cpp := Expr "*%arg(r)";
     operation_contract :=
       PureOperation
         [{| argument_name := "r"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "r"; path_components := ["contents"] |}] |}%pstring.

#[global] Instance write_ref_mapping : OperationMapping (Ref (@write_ref)) :=
  {| operation_headers := [];
     operation_cpp := Expr "*%arg(r) = %arg(a)";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "r"; argument_use := Write |};
          {| argument_name := "a"; argument_use := Take |}]
         ReturnValue
         [WritesComponent {| path_argument := "r"; path_components := ["contents"] |} (Some "a");
          InvalidatesElementBorrows {| path_argument := "r"; path_components := ["contents"] |}] |}%pstring.

#[global] Instance array_mapping (R : Refs) (A : Type) : TypeMapping (@array R A) :=
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

(** [Read] gives the template the read view, [std::span<const A>]. *)
#[global] Instance read_array_mapping : OperationMapping (Ref (@read_array)) :=
  {| operation_headers := ["span"];
     operation_cpp := Structured (Index (Arg "arr") (Arg "i"));
     operation_contract :=
       PureOperation
         [{| argument_name := "arr"; argument_use := Read |};
          {| argument_name := "i"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "arr"; path_components := ["contents"] |}] |}%pstring.

(** [Write] gives the template the writable view, [std::span<A>].  Writing
    an element does not reallocate the storage: it invalidates borrows of
    the old element, not views of the array. *)
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

#[global] Instance array_to_list_mapping : OperationMapping (Ref (@array_to_list)) :=
  {| operation_headers := ["crane_st.h"];
     operation_cpp := Structured (Call "crane::st::elems" [Apply "List" [TypeArg (StoredComponent "contents")]] [(Arg "arr")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "arr"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "arr"; path_components := ["contents"] |}] |}%pstring.

Crane Extraction Implicit swap_array [R].

(** [Write] gives the template the writable view, [std::span<A>]. *)
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
