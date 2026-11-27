(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A typed mapping's copy and access models decide how a parameter that
    is only read is passed, with no list of C++ type names involved:

    - [Flag], mapped to [bool] with [BitCopy] and [ReadByValue]: by value.
    - [Bag A], mapped to [std::vector<%stored(element)>] with
      [DuplicateValue] and [ReadByConstReference]: by [const&].
    - [Cell A], mapped to [std::array<%stored(element), 1>] with
      [CopyComponents ["element"]] and [ReadByComponents ["element"]]: by
      value at [Cell Flag], by [const&] at [Cell (Bag nat)].

    The program also uses [option], mapped by the legacy
    [Crane Extract Inductive] of [Mapping.Std]: legacy and typed mappings
    coexist in one program. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatInt.

Open Scope pstring_scope.

Inductive Flag : Type := up | down.

Inductive Bag (A : Type) : Type := bag_empty | bag_one (x : A).
Arguments bag_empty {A}.
Arguments bag_one {A} x.

Inductive Cell (A : Type) : Type := cell (x : A).
Arguments cell {A} x.

#[export] Instance flag_mapping : TypeMapping Flag :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Name "bool";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews Flag;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref up;
             ctor_build := Expr "true";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut"; case_fields := [] |} |};
          {| ctor_source := Ref down;
             ctor_build := Expr "false";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "!%scrut"; case_fields := [] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance bag_mapping (A : Type) : TypeMapping (Bag A) :=
  {| type_headers := ["vector"];
     type_cpp :=
       Crane.Cpp.Apply "std::vector"
         [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components :=
       [{| component_name := "element"; component_type := KnownType A |}];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (Bag A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@bag_empty A);
             ctor_build := Expr "std::vector<%stored(element)>{}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.empty()"; case_fields := [] |} |};
          {| ctor_source := Ref (@bag_one A);
             ctor_build := Expr "std::vector<%stored(element)>{%a0}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.empty()";
                       case_fields := [(0, CanonicalBorrowProjection "%scrut.front()")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance cell_mapping (A : Type) : TypeMapping (Cell A) :=
  {| type_headers := ["array"];
     type_cpp :=
       Crane.Cpp.Apply "std::array"
         [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element");
          Crane.Cpp.ValueArg "1"];
     type_components :=
       [{| component_name := "element"; component_type := KnownType A |}];
     type_copy := CopyComponents ["element"];
     type_access := ReadOnlyValue (ReadByComponents ["element"]);
     type_views := NoViews (Cell A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@cell A);
             ctor_build := Expr "std::array<%stored(element), 1>{%a0}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "true";
                       case_fields := [(0, CanonicalBorrowProjection "%scrut[0]")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

Module TypedMappingCopy.

Definition flag_both (a b : Flag) : Flag :=
  match a with up => b | down => down end.

Definition bag_count (b : Bag nat) : nat :=
  match b with bag_empty => 0 | bag_one x => x end.

Definition cell_flag (c : Cell Flag) : Flag := match c with cell f => f end.

Definition cell_bag_count (c : Cell (Bag nat)) : nat :=
  match c with cell b => bag_count b end.

Definition make_cell (n : nat) : Cell (Bag nat) := cell (bag_one n).

Definition flag_of_option (o : option Flag) : Flag :=
  match o with Some f => f | None => down end.

Definition bag_of_option (o : option nat) : Bag nat :=
  match o with Some n => bag_one n | None => bag_empty end.

End TypedMappingCopy.

Crane Extraction "typed_mapping_copy" TypedMappingCopy.
