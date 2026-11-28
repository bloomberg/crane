(* SPDX-License-Identifier: BSD-3-Clause *)
(** Opt-in extraction mapping: Coq [list] -> C++ [immer::flex_vector], with
    COMPLETENESS-AWARE ELEMENT WRAPPING (see ~/crane/WRAP.md).

    immer containers require a *complete* element type, but Coq lists are often
    recursive. The [BoxedComponent] box ([immer::box]) tells Crane to wrap
    the element in [immer::box] *only at recursive occurrences* (element types
    that recurse through the list, e.g. [json_value]). Flat elements — [char]
    (the lexer's hot path), [bool], [string*string] — stay UNBOXED.

    - [%elem]  in the type/nil templates = the (possibly boxed) element slot;
      Crane fills it with [immer::box<T>] when [T] is recursive, else [T].
    - [%t0]/[%aN] in the match/cons templates stay bare; immer::box's implicit
      conversions (ctor from T, operator const T&) make cons/match work for both.

    Requires immer headers on the include path: -I $(HOME)/cpp/immer. *)
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
  {| type_headers := ["immer/flex_vector.hpp"; "immer/box.hpp"];
     type_cpp := Crane.Cpp.Apply "immer::flex_vector" [Crane.Cpp.TypeArg (Crane.Cpp.BoxedComponent "element" (Crane.Cpp.Apply "immer::box" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")]))];
     type_components :=
       [{| component_name := "element"; component_type := FieldType (Ref (@cons A)) 0 |}];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (list A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@nil A);
             ctor_build := Expr "immer::flex_vector<%stored(element)>{}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.empty()"; case_fields := [] |} |};
          {| ctor_source := Ref (@cons A);
             ctor_build := Expr "%a1.push_front(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.empty()";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "%scrut.front()");
                          (1, OwnedProjection "%scrut.drop(1)")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := DrainWith "for (const auto& _e : %scrut) { %yield(_e); }";
     type_numerals := None |}.
End ListMapping.

(** Core list functions that are element-representation-agnostic. *)
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance length_mapping : OperationMapping (Ref (@Datatypes.length)) :=
  pure_cpp ["cstdint"] ["l"]
    (Expr "static_cast<uint64_t>(%arg(l).size())").

(* flex_vector concatenation is O(log N) structural and works for both boxed and
   unboxed element reps (both sides are the same flex_vector<%elem>). *)
#[global] Instance app_mapping : OperationMapping (Ref (@Datatypes.app)) :=
  pure_cpp ["immer/flex_vector.hpp"] ["l"; "m"]
    (Structured (Binop (Add Unchecked) (Arg "l") (Arg "m"))).

(** String <-> list conversions. [list ascii] = [char] elements, which are never
    recursive, hence always UNBOXED [flex_vector<char>]. *)
#[global] Instance list_ascii_of_string_mapping : OperationMapping (Ref (@String.list_ascii_of_string)) :=
  pure_cpp ["immer/flex_vector.hpp"] ["s"]
    (Expr "[&]() { const auto& _s = %arg(s); return immer::flex_vector<char>(_s.begin(), _s.end()); }()").

#[global] Instance string_of_list_ascii_mapping : OperationMapping (Ref (@String.string_of_list_ascii)) :=
  pure_cpp ["string"] ["s"]
    (Expr "[&]() { std::string _r; for (const auto& _c : %arg(s)) _r.push_back(_c); return _r; }()").

(* Higher-order list functions (map/rev/filter/fold_*/forallb/…) are intentionally
   NOT mapped: Crane extracts their Coq definitions recursively using the
   inductive nil/cons/match templates above, which already box-or-not per element
   type consistently. This keeps boxing logic in one place. *)
