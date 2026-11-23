(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction mappings shared by all C++ flavors (Std, BDE).

    Maps [bool] and [sumbool] to C++ [bool], [unit] to [std::monostate], and
    [PrimArray.array] to [persistent_array<T>], as typed mappings: they
    activate on [Import].  Imported transitively by [Mapping.Std] and
    [Mapping.BDE]. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

(** [true] is tested by the value itself and is listed first; [false] is
    what remains. *)
#[export] Instance bool_mapping : TypeMapping bool :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Name "bool";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews bool;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref true;
             ctor_build := Expr "true";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut";
                       case_fields := [] |} |};
          {| ctor_source := Ref false;
             ctor_build := Expr "false";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "!%scrut";
                       case_fields := [] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** A [sumbool]'s proofs are erased: it is the [bool] of which side holds. *)
#[export] Instance sumbool_mapping (A B : Prop) : TypeMapping (sumbool A B) :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Name "bool";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews (sumbool A B);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@left A B);
             ctor_build := Expr "true";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut";
                       case_fields := [] |} |};
          {| ctor_source := Ref (@right A B);
             ctor_build := Expr "false";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "!%scrut";
                       case_fields := [] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance negb_mapping : OperationMapping (Ref negb) :=
  {| operation_headers := [];
     operation_cpp := Expr "!(%arg(b))";
     operation_contract :=
       PureOperation [{| argument_name := "b"; argument_use := Read |}] ReturnValue [] |}.
#[export] Instance andb_mapping : OperationMapping (Ref andb) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(b1) && %arg(b2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "b1"; argument_use := Read |};
          {| argument_name := "b2"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance orb_mapping : OperationMapping (Ref orb) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(b1) || %arg(b2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "b1"; argument_use := Read |};
          {| argument_name := "b2"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance unit_mapping : TypeMapping unit :=
  {| type_headers := ["variant"];
     type_cpp := Crane.Cpp.Name "std::monostate";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews unit;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref tt;
             ctor_build := Expr "std::monostate{}";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "true";
                       case_fields := [] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** [PrimArray.array A] is a [persistent_array] (theories/cpp/
    persistent_array.h): a copy-on-write array, read by const reference. *)
From Corelib Require PrimArray.
#[export] Instance prim_array_mapping (A : Type) : TypeMapping (PrimArray.array A) :=
  {| type_headers := ["persistent_array.h"];
     type_cpp :=
       Crane.Cpp.Apply "persistent_array"
         [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components :=
       [{| component_name := "element"; component_type := KnownType A |}];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (PrimArray.array A);
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
#[export] Instance prim_array_make_mapping : OperationMapping (Ref (@PrimArray.make)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "persistent_array<%t0>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance prim_array_get_mapping : OperationMapping (Ref (@PrimArray.get)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "%arg(x).get(%arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance prim_array_default_mapping : OperationMapping (Ref (@PrimArray.default)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "%arg(x).default_value()";
     operation_contract :=
       PureOperation [{| argument_name := "x"; argument_use := Read |}] ReturnValue [] |}.
#[export] Instance prim_array_set_mapping : OperationMapping (Ref (@PrimArray.set)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "%arg(x).set(%arg(y), %arg(z))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |};
          {| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance prim_array_length_mapping : OperationMapping (Ref (@PrimArray.length)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "%arg(x).length()";
     operation_contract :=
       PureOperation [{| argument_name := "x"; argument_use := Read |}] ReturnValue [] |}.
#[export] Instance prim_array_copy_mapping : OperationMapping (Ref (@PrimArray.copy)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "%arg(x).copy()";
     operation_contract :=
       PureOperation [{| argument_name := "x"; argument_use := Read |}] ReturnValue [] |}.
