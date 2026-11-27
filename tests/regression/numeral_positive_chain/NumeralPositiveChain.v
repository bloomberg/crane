(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [positive] registered as a numeral: its literals are binary chains,
    not Peano ones, though [xO] is its last unary constructor and [xH] its
    last nullary one. *)

From Stdlib Require Import BinNums.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.

From Crane Require Mapping.Descriptor.
From Corelib Require PrimString.
From Stdlib Require List.
Module PositiveMapping.
Import Crane.Mapping.Descriptor PrimString.PStringNotations List.ListNotations.
Local Open Scope pstring_scope.
#[global] Instance positive_mapping : TypeMapping positive :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Int Crane.Cpp.U64;
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews positive;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref xH; ctor_build := Expr "UINT64_C(1)";
             ctor_view := Some {| view_requirement := CanonicalObservation; case_test := "%scrut == 1"; case_fields := [] |} |};
          {| ctor_source := Ref xI; ctor_build := Expr "(2 * %a0 + 1)";
             ctor_view := Some {| view_requirement := CanonicalObservation; case_test := "%scrut % 2";
                                  case_fields := [(0, OwnedProjection "%scrut / 2")] |} |};
          {| ctor_source := Ref xO; ctor_build := Expr "(2 * %a0)";
             ctor_view := Some {| view_requirement := CanonicalObservation; case_test := "true";
                                  case_fields := [(0, OwnedProjection "%scrut / 2")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref xH; numeral_action := NumeralOne |};
                  {| numeral_constructor := Ref xO; numeral_action := NumeralDouble 0 |};
                  {| numeral_constructor := Ref xI; numeral_action := NumeralDoublePlusOne 0 |}];
               numeral_emitter := IntegerToken "UINT64_C(" ")";
               numeral_converters := [] |} |}.
End PositiveMapping.

Module NumeralPositiveChain.

Definition two : positive := xO xH.
Definition four : positive := xO (xO xH).
Definition five : positive := xI (xO xH).
Definition six : positive := xO (xI xH).

End NumeralPositiveChain.

Crane Extraction "numeral_positive_chain" NumeralPositiveChain.
