(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extracts [Ascii.ascii] to C++ [char], as OCaml's [ExtrOcamlString]
    extracts it to OCaml's [char], as a typed mapping:
    it activates on [Import].

    An [ascii] is otherwise a record of eight [bool]s, and comparing two of
    them goes through [N_of_ascii]: a list of their bits, then a binary
    natural built from it.  Code that compares identifiers character by
    character pays that for every character.  Mapped, a character is one
    byte and comparing two is one instruction.

    The constructor packs its eight bits, least significant first; a match
    unpacks them.  [compare], [eqb] and [ascii_dec] compare bytes.
    [compare]'s result is the [comparison] enum, whose constructors are
    numbered in declaration order ([Eq], [Lt], [Gt]); [%ret] names the enum
    whatever the generator calls it.

    The constructor's eight fields, a match's projections, and the results
    of [eqb] and [ascii_dec] are C++ [bool]s: the mapping is written against
    [Mapping.Shared]'s [bool] and [sumbool], which it exports, so a program
    importing it alone does not meet the generated [bool] enum. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Shared.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import Ascii List.
Import ListNotations.
Local Open Scope pstring_scope.

#[export] Instance ascii_mapping : TypeMapping ascii :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Name "char";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews ascii;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref Ascii;
             ctor_build := Expr "static_cast<char>((%a0 ? 1 : 0) | (%a1 ? 2 : 0) | (%a2 ? 4 : 0) | (%a3 ? 8 : 0) | (%a4 ? 16 : 0) | (%a5 ? 32 : 0) | (%a6 ? 64 : 0) | (%a7 ? 128 : 0))";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "true";
                       case_fields :=
                         [(0, OwnedProjection "(static_cast<unsigned char>(%scrut) & 1) != 0");
                          (1, OwnedProjection "(static_cast<unsigned char>(%scrut) & 2) != 0");
                          (2, OwnedProjection "(static_cast<unsigned char>(%scrut) & 4) != 0");
                          (3, OwnedProjection "(static_cast<unsigned char>(%scrut) & 8) != 0");
                          (4, OwnedProjection "(static_cast<unsigned char>(%scrut) & 16) != 0");
                          (5, OwnedProjection "(static_cast<unsigned char>(%scrut) & 32) != 0");
                          (6, OwnedProjection "(static_cast<unsigned char>(%scrut) & 64) != 0");
                          (7, OwnedProjection "(static_cast<unsigned char>(%scrut) & 128) != 0")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance ascii_compare_mapping : OperationMapping (Ref Ascii.compare) :=
  {| operation_headers := [];
     operation_cpp := Expr "[](char _x, char _y) { return static_cast<%ret>(_x == _y ? 0 : (static_cast<unsigned char>(_x) < static_cast<unsigned char>(_y) ? 1 : 2)); }(%arg(a), %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance ascii_eqb_mapping : OperationMapping (Ref Ascii.eqb) :=
  {| operation_headers := ["functional"];
     operation_cpp := Expr "std::equal_to<char>{}(%arg(a), %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance ascii_dec_mapping : OperationMapping (Ref Ascii.ascii_dec) :=
  {| operation_headers := ["functional"];
     operation_cpp := Expr "std::equal_to<char>{}(%arg(a), %arg(b))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
