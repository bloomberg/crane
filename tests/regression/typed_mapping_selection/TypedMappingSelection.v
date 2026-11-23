(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Typed mappings are selected by import.

    [MappingA] and [MappingB] map the type [Pixel] and the operation
    [brighten] differently.  Importing only one selects it; importing both
    is an ambiguity that names both instances, whatever their priorities;
    importing neither leaves [Pixel] unmapped.  The checks run while
    TypedMappingSelection.vo is built; the extraction at the end does not
    use the mappings (they are not lowered yet). *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Open Scope pstring_scope.

Inductive Pixel : Type := pixel (level : nat).

Definition brighten (p : Pixel) : Pixel :=
  match p with pixel n => pixel (S n) end.

Module MappingA.
  #[export] Instance pixel_mapping : TypeMapping Pixel :=
    {| type_headers := ["cstdint"];
       type_cpp := Crane.Cpp.Name "std::uint8_t";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Pixel;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.

  #[export] Instance brighten_mapping : OperationMapping (Ref brighten) :=
    {| operation_headers := [];
       operation_cpp := Expr "static_cast<std::uint8_t>(%arg(p) + 1)";
       operation_contract :=
         PureOperation
           [{| argument_name := "p"; argument_use := Read |}]
           ReturnValue
           [] |}.
End MappingA.

Module MappingB.
  #[export] Instance pixel_mapping : TypeMapping Pixel | 0 :=
    {| type_headers := ["string"];
       type_cpp := Crane.Cpp.Name "std::string";
       type_components := [];
       type_copy := DuplicateValue;
       type_access := ReadOnlyValue ReadByConstReference;
       type_views := NoViews Pixel;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.

  #[export] Instance brighten_mapping : OperationMapping (Ref brighten) | 0 :=
    {| operation_headers := [];
       operation_cpp := Expr "(%arg(p) + ""+"")";
       operation_contract :=
         PureOperation
           [{| argument_name := "p"; argument_use := Read |}]
           ReturnValue
           [] |}.
End MappingB.

Module NoneImported.
  Crane Check Mapping Pixel Unmapped.
  Crane Check Mapping brighten Unmapped.
End NoneImported.

Module OnlyA.
  Import MappingA.
  Crane Check Mapping Pixel Selects MappingA.pixel_mapping.
  Crane Check Mapping brighten Selects MappingA.brighten_mapping.
  Crane Show Mapping Pixel.
End OnlyA.

Module OnlyB.
  Import MappingB.
  Crane Check Mapping Pixel Selects MappingB.pixel_mapping.
  Crane Check Mapping brighten Selects MappingB.brighten_mapping.
End OnlyB.

Module Both.
  Import MappingA MappingB.
  Crane Check Mapping Pixel Fails With
    "Ambiguous type mapping for Pixel: the instances
     CraneTestsRegression.typed_mapping_selection.TypedMappingSelection.MappingA.pixel_mapping,
     CraneTestsRegression.typed_mapping_selection.TypedMappingSelection.MappingB.pixel_mapping
     all apply".
  Crane Check Mapping brighten Fails With
    "Ambiguous operation mapping for brighten: the instances
     CraneTestsRegression.typed_mapping_selection.TypedMappingSelection.MappingA.brighten_mapping,
     CraneTestsRegression.typed_mapping_selection.TypedMappingSelection.MappingB.brighten_mapping
     all apply".
End Both.

Module Sample.
  Definition answer : nat := 42.
End Sample.

Crane Extraction "typed_mapping_selection" Sample.
