(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Compiled interfaces (src/base/mapping_interface.mli), the library
    half: [Meter] has two incompatible typed mappings, [Narrow]
    ([std::uint32_t]) and [Wide] ([std::uint64_t]).  [Lib] is extracted on
    its own into [typed_mapping_interface_lib.{h,cpp}] with [Narrow]
    imported, and the unit records that it was written against [Narrow].
    [Use.v] includes that header with [Narrow] imported too;
    [Mismatch.v] resolves [Meter] differently and is refused. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor Mapping.NatInt.
Local Open Scope pstring_scope.

Inductive Meter : Type := meter (n : nat).

Module Narrow.
  #[export] Instance meter_narrow : TypeMapping Meter :=
    {| type_headers := ["cstdint"];
       type_cpp := Crane.Cpp.Name "std::uint32_t";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Meter;
       type_interface :=
         AlgebraicInterface
           [{| ctor_source := Ref meter;
               ctor_build := Expr "static_cast<std::uint32_t>(%a0)";
               ctor_view :=
                 Some {| view_requirement := PreferredObservation;
                         case_test := "true";
                         case_fields := [(0, OwnedProjection "static_cast<uint64_t>(%scrut)")] |} |}];
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
End Narrow.

Module Wide.
  #[export] Instance meter_wide : TypeMapping Meter :=
    {| type_headers := ["cstdint"];
       type_cpp := Crane.Cpp.Name "std::uint64_t";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Meter;
       type_interface :=
         AlgebraicInterface
           [{| ctor_source := Ref meter;
               ctor_build := Expr "static_cast<std::uint64_t>(%a0)";
               ctor_view :=
                 Some {| view_requirement := PreferredObservation;
                         case_test := "true";
                         case_fields := [(0, OwnedProjection "static_cast<uint64_t>(%scrut)")] |} |}];
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
End Wide.

Import Narrow.

Module Lib.
  Definition double (m : Meter) : Meter := match m with meter n => meter (n + n) end.
  Definition value (m : Meter) : nat := match m with meter n => n end.
End Lib.

Crane Extraction "typed_mapping_interface_lib" Lib.
