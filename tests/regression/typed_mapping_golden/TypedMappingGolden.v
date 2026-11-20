(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Typed mappings written with the descriptor library's constructors and
    records only (design 4.4, 24.2).  The file is documentation: each
    instance spells out every choice, with no helper functions.

    - [Color]: an enumeration mapped to a C++ enum, with an algebraic
      interface (how each constructor is built and tested).
    - [Buffer A]: a parametric mutable buffer mapped to [std::vector<A>],
      with a read span and a writable span (design 14.7).
    - [Handle]: an identity handle mapped to a raw pointer, owned by an
      external allocator.
    - [buffer_set], [buffer_length]: operations on [Buffer A].

    The checks below resolve, decode and validate each mapping while
    TypedMappingGolden.vo is built; the extraction at the end does not use
    the mappings (they are not lowered yet). *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Open Scope pstring_scope.

Inductive Color : Type := Red | Green | Blue.

Record Buffer (A : Type) : Type := mk_buffer { elements : list A }.

Axiom Handle : Type.
(** The region owning every [Handle]; a definition, so [Ref handle_pool]
    shows that a referenced declaration is not unfolded. *)
Definition handle_pool : unit := tt.

Definition buffer_set {A : Type} (buffer : Buffer A) (index : nat) (value : A)
  : Buffer A := buffer.

Definition buffer_length {A : Type} (buffer : Buffer A) : nat :=
  length (elements A buffer).

#[export] Instance color_mapping : TypeMapping Color :=
  {| type_headers := ["palette.h"];
     type_cpp := Crane.Cpp.Name "palette::color";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews Color;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref Red;
             ctor_build := Expr "palette::color::red";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == palette::color::red";
                       case_fields := [] |} |};
          {| ctor_source := Ref Green;
             ctor_build := Expr "palette::color::green";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == palette::color::green";
                       case_fields := [] |} |};
          {| ctor_source := Ref Blue;
             ctor_build := Expr "palette::color::blue";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == palette::color::blue";
                       case_fields := [] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance buffer_mapping (A : Type) : TypeMapping (Buffer A) :=
  {| type_headers := ["span"; "vector"];
     type_cpp :=
       Crane.Cpp.Apply "std::vector"
         [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components :=
       [{| component_name := "element"; component_type := KnownType A |}];
     type_copy := DuplicateValue;
     type_access := MutableValue ReadByConstReference;
     type_views :=
       ReadWriteViews
         {| view_headers := ["span"];
            view_cpp :=
              Crane.Cpp.Apply "std::span"
                [Crane.Cpp.TypeArg
                  (Crane.Cpp.Const (Crane.Cpp.StoredComponent "element"))];
            view_from_canonical := "std::span<const %stored(element)>{%value}";
            view_escape :=
              MaterialiseView
                (Expr "std::vector<%stored(element)>{%view.begin(), %view.end()}") |}
         {| view_headers := ["span"];
            view_cpp :=
              Crane.Cpp.Apply "std::span"
                [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
            view_from_canonical := "std::span<%stored(element)>{%value}";
            view_escape := BorrowOnly |}
         "std::span<const %stored(element)>{%view}";
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@mk_buffer A);
             ctor_build :=
               WithBody "std::vector<%stored(element)>{}"
                 "for (const auto &x : %a0) { %result.push_back(x); }";
             ctor_view := None |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance handle_mapping : TypeMapping Handle :=
  {| type_headers := ["pool.h"];
     type_cpp := Crane.Cpp.Pointer (Crane.Cpp.Name "pool::object");
     type_components := [];
     type_copy := BitCopy;
     type_access := MutableHandle HandleByValue;
     type_views := NoViews Handle;
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := RegionOwned (Ref handle_pool);
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance buffer_set_mapping (A : Type)
  : OperationMapping (Ref (@buffer_set A)) :=
  {| operation_headers := ["utility"];
     operation_cpp := Expr "%arg(buffer)[%arg(index)] = std::move(%arg(value))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "buffer"; argument_use := Write |};
          {| argument_name := "index"; argument_use := Read |};
          {| argument_name := "value"; argument_use := Take |}]
         ReturnValue
         [WritesComponent
            {| path_argument := "buffer"; path_components := ["element"] |}
            (Some "value");
          InvalidatesElementBorrows
            {| path_argument := "buffer"; path_components := ["element"] |}] |}.

#[export] Instance buffer_length_mapping (A : Type)
  : OperationMapping (Ref (@buffer_length A)) :=
  {| operation_headers := ["cstdint"];
     operation_cpp := Expr "static_cast<std::uint64_t>(%arg(buffer).size())";
     operation_contract :=
       PureOperation
         [{| argument_name := "buffer"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent
            {| path_argument := "buffer"; path_components := ["element"] |}] |}.

Crane Check Mapping Color Selects color_mapping.
Crane Check Mapping (Buffer nat) Selects buffer_mapping.
Crane Check Mapping (Buffer bool) Selects buffer_mapping.
Crane Check Mapping Handle Selects handle_mapping.
Crane Check Mapping (@buffer_set nat) Selects buffer_set_mapping.
Crane Check Mapping (@buffer_length bool) Selects buffer_length_mapping.
Crane Check Mapping nat Unmapped.

(* The decoded descriptors keep [Ref (@mk_buffer nat)] and [Ref handle_pool]
   as references. *)
Crane Show Mapping (Buffer nat).
Crane Show Mapping Handle.
Crane Show Mapping (@buffer_set nat).

Module Sample.
  Definition answer : nat := 42.
End Sample.

Crane Extraction "typed_mapping_golden" Sample.
