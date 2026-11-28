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

(** [bool] is C++ [bool]: [true] is tested by the value itself and is
    listed first; [false] is what remains. *)
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

(** A [sig]'s proof is erased, so a [sig] is its witness: [exist x h] is
    [x], and a match binds the witness to the value itself.  [sig2] has two
    erased proofs and is its witness too. *)
#[export] Instance sig_mapping (A : Type) (P : A -> Prop) : TypeMapping (sig P) :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.StoredComponent "witness";
     type_components :=
       [{| component_name := "witness";
           component_type := FieldType (Ref (@exist A P)) 0 |}];
     type_copy := CopyComponents ["witness"];
     type_access := ReadOnlyValue (ReadByComponents ["witness"]);
     type_views := NoViews (sig P);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@exist A P);
             ctor_build := Expr "%a0";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "true";
                       case_fields := [(0, CanonicalBorrowProjection "%scrut")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** [sig2] is its witness too, both proofs erased. *)
#[export] Instance sig2_mapping (A : Type) (P Q : A -> Prop) : TypeMapping (sig2 P Q) :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.StoredComponent "witness";
     type_components :=
       [{| component_name := "witness";
           component_type := FieldType (Ref (@exist2 A P Q)) 0 |}];
     type_copy := CopyComponents ["witness"];
     type_access := ReadOnlyValue (ReadByComponents ["witness"]);
     type_views := NoViews (sig2 P Q);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@exist2 A P Q);
             ctor_build := Expr "%a0";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "true";
                       case_fields := [(0, CanonicalBorrowProjection "%scrut")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** [proj1_sig] is the witness, in place. *)
#[export] Instance proj1_sig_mapping : OperationMapping (Ref (@proj1_sig)) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(e)";
     operation_contract :=
       PureOperation [{| argument_name := "e"; argument_use := Read |}]
         (ReturnBorrowed CanonicalBorrow {| path_argument := "e"; path_components := ["witness"] |}) [] |}.

(** A [sumbool] is the [bool] of which side holds, so the [sumbool] of a
    [bool] is that [bool]. *)
#[export] Instance sumbool_of_bool_mapping : OperationMapping (Ref Sumbool.sumbool_of_bool) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(b)";
     operation_contract :=
       PureOperation [{| argument_name := "b"; argument_use := Read |}] ReturnValue [] |}.

(** [negb] is [!]. *)
#[export] Instance negb_mapping : OperationMapping (Ref negb) :=
  {| operation_headers := [];
     operation_cpp := Expr "!(%arg(b))";
     operation_contract :=
       PureOperation [{| argument_name := "b"; argument_use := Read |}] ReturnValue [] |}.
(** [andb] is [&&]. *)
#[export] Instance andb_mapping : OperationMapping (Ref andb) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(b1) && %arg(b2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "b1"; argument_use := Read |};
          {| argument_name := "b2"; argument_use := Read |}]
         ReturnValue [] |}.
(** [orb] is [||]. *)
#[export] Instance orb_mapping : OperationMapping (Ref orb) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(b1) || %arg(b2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "b1"; argument_use := Read |};
          {| argument_name := "b2"; argument_use := Read |}]
         ReturnValue [] |}.

(** [unit] is [std::monostate]; a match on [tt] needs no test. *)
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

From Corelib Require PrimArray.
(** [PrimArray.array A] is a [persistent_array] (theories/cpp/
    persistent_array.h): a copy-on-write array, read by const reference. *)
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
(** [make n x] is [n] copies of [x], [x] also the default; the length is
    clamped to [max_length], as in Rocq. *)
#[export] Instance prim_array_make_mapping : OperationMapping (Ref (@PrimArray.make)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "persistent_array<%t0>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [get a i] is [a.get(i)]: the default out of bounds, as in Rocq. *)
#[export] Instance prim_array_get_mapping : OperationMapping (Ref (@PrimArray.get)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "%arg(x).get(%arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [default a] is the element out-of-bounds reads give. *)
#[export] Instance prim_array_default_mapping : OperationMapping (Ref (@PrimArray.default)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "%arg(x).default_value()";
     operation_contract :=
       PureOperation [{| argument_name := "x"; argument_use := Read |}] ReturnValue [] |}.
(** [set a i x] is [a.set(i, x)], a new array (updated in place only when
    [a] is an unshared temporary); out of bounds it is [a]. *)
#[export] Instance prim_array_set_mapping : OperationMapping (Ref (@PrimArray.set)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "%arg(x).set(%arg(y), %arg(z))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |};
          {| argument_name := "z"; argument_use := Read |}]
         ReturnValue [] |}.
(** [length a] is [a.length()]. *)
#[export] Instance prim_array_length_mapping : OperationMapping (Ref (@PrimArray.length)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "%arg(x).length()";
     operation_contract :=
       PureOperation [{| argument_name := "x"; argument_use := Read |}] ReturnValue [] |}.
(** [copy a] is [a.copy()], a deep copy. *)
#[export] Instance prim_array_copy_mapping : OperationMapping (Ref (@PrimArray.copy)) :=
  {| operation_headers := ["persistent_array.h"];
     operation_cpp := Expr "%arg(x).copy()";
     operation_contract :=
       PureOperation [{| argument_name := "x"; argument_use := Read |}] ReturnValue [] |}.
