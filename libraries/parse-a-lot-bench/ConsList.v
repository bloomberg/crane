(* SPDX-License-Identifier: BSD-3-Clause *)
(** Opt-in extraction mapping: Coq [list] -> C++ [crane::list] (an immutable,
    persistent, singly-linked cons list; see ~/crane/theories/cpp/conslist.h).

    Rationale: [cons] is the dominant list op in extracted functional code and is
    O(1) here (vs O(log n)+alloc for immer::flex_vector::push_front, ~17x slower
    in a microbenchmark).  [head]/[tail]/[drop 1] are O(1) too, which also helps
    the lexer's drop-per-char hot path.  Trade-off: [app]/[length] are O(n).

    No element boxing is needed: recursion goes through the cell's [crane::rc]
    tail, so a recursive element type (e.g. json_value containing list json_value)
    stays a bare, complete-enough field. This drops immer::box entirely. *)
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Extraction.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

Module ListMapping.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance list_mapping (A : Type) : TypeMapping (list A) :=
  {| type_headers := ["conslist.h"];
     type_cpp := Crane.Cpp.Apply "crane::list" [Crane.Cpp.TypeArg (Crane.Cpp.BoxedComponent "element" (Crane.Cpp.Apply "crane::box" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")]))];
     type_components :=
       [{| component_name := "element"; component_type := FieldType (Ref (@cons A)) 0 |}];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (list A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@nil A);
             ctor_build := Expr "crane::list<%stored(element)>{}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.empty()"; case_fields := [] |} |};
          {| ctor_source := Ref (@cons A);
             ctor_build := Expr "crane::cons(%a0, %a1)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.empty()";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "%scrut.front()");
                          (1, OwnedProjection "%scrut.tail()")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := DrainWith "%scrut.drain_each([&](auto&& _e) { %yield(std::move(_e)); });";
     type_numerals := None |}.
End ListMapping.

Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance length_mapping : OperationMapping (Ref (@Datatypes.length)) :=
  pure_cpp ["cstdint"] ["l"]
    (Expr "static_cast<uint64_t>(%arg(l).size())").

#[global] Instance app_mapping : OperationMapping (Ref (@Datatypes.app)) :=
  pure_cpp ["conslist.h"] ["l"; "m"]
    (Expr "crane::list<%t0>::app(%arg(l), %arg(m))").

#[global] Instance list_ascii_of_string_mapping : OperationMapping (Ref (@String.list_ascii_of_string)) :=
  pure_cpp ["conslist.h"] ["s"]
    (Expr "[&]() { const auto& _s = %arg(s); return crane::list<char>::from_range(_s.begin(), _s.end()); }()").

#[global] Instance string_of_list_ascii_mapping : OperationMapping (Ref (@String.string_of_list_ascii)) :=
  pure_cpp ["string"] ["s"]
    (Expr "[&]() { std::string _r; for (const auto& _c : %arg(s)) _r.push_back(_c); return _r; }()").
