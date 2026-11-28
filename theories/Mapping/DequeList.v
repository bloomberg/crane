(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Opt-in extraction mapping: Coq [list] -> C++ [std::deque], as typed
    mappings: they activate on [Import].

    Import this module to extract Coq lists as [std::deque<T>]
    instead of the default [Datatypes::List<T>] linked-list.

    [std::deque] provides O(1) amortized push_front/push_back,
    O(1) indexed access, and cache-friendly chunked storage. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
Import ListNotations.
Local Open Scope pstring_scope.

(** A deque copies every element, so it is read by const reference.  A
    match tests [nil] first; [cons] views the front by reference and the
    rest as a copy (the logical tail of a deque is not a part of it, so a
    head-tail recursion is quadratic). *)
#[export] Instance deque_list_mapping (A : Type) : TypeMapping (list A) :=
  {| type_headers := ["deque"];
     type_cpp :=
       Crane.Cpp.Apply "std::deque"
         [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components :=
       [{| component_name := "element";
           component_type := FieldType (Ref (@cons A)) 0 |}];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (list A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@nil A);
             ctor_build := Expr "std::deque<%stored(element)>{}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.empty()";
                       case_fields := [] |} |};
          {| ctor_source := Ref (@cons A);
             ctor_build := Expr "[](auto _a0, auto _a1) { _a1.push_front(_a0); return _a1; }(%a0, %a1)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.empty()";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "%scrut.front()");
                          (1, OwnedProjection "%ret(%scrut.begin() + 1, %scrut.end())")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** Core list functions from [Datatypes], higher-order functions from
    [List], and the string conversions.  A result is declared at [%ret],
    the type translation recorded for the call. *)
#[export] Instance deque_length_mapping : OperationMapping (Ref (@Datatypes.length)) :=
  {| operation_headers := ["cstdint"];
     operation_cpp := Expr "static_cast<uint64_t>(%arg(l).size())";
     operation_contract :=
       PureOperation
         [{| argument_name := "l"; argument_use := Read |}]
         ReturnValue [] |}.
(** [app l m] copies [l] and appends [m]'s elements. *)
#[export] Instance deque_app_mapping : OperationMapping (Ref (@Datatypes.app)) :=
  {| operation_headers := ["deque"];
     operation_cpp := Expr "[](auto _r, const auto& _s) { _r.insert(_r.end(), _s.begin(), _s.end()); return _r; }(%arg(l), %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "l"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
(** [map f l] pushes [f x] for each [x], front to back. *)
#[export] Instance deque_map_mapping : OperationMapping (Ref (@List.map)) :=
  {| operation_headers := ["deque"; "utility"; "type_traits"];
     operation_cpp := Expr "[](auto _f, const auto& _l) { %ret _r; for (const auto& _x : _l) _r.push_back(_f(_x)); return _r; }(%arg(f), %arg(l))";
     operation_contract :=
       PureOperation
         [{| argument_name := "f"; argument_use := Read |};
          {| argument_name := "l"; argument_use := Read |}]
         ReturnValue [] |}.
(** [rev l] reverses a copy with [std::reverse]. *)
#[export] Instance deque_rev_mapping : OperationMapping (Ref (@List.rev)) :=
  {| operation_headers := ["algorithm"];
     operation_cpp := Expr "[](auto _r) { std::reverse(_r.begin(), _r.end()); return _r; }(%arg(l))";
     operation_contract :=
       PureOperation
         [{| argument_name := "l"; argument_use := Read |}]
         ReturnValue [] |}.
(** [filter f l] keeps the elements [f] accepts, in order. *)
#[export] Instance deque_filter_mapping : OperationMapping (Ref (@List.filter)) :=
  {| operation_headers := ["deque"];
     operation_cpp := Expr "[](auto _f, const auto& _l) { %ret _r; for (const auto& _x : _l) if (_f(_x)) _r.push_back(_x); return _r; }(%arg(f), %arg(l))";
     operation_contract :=
       PureOperation
         [{| argument_name := "f"; argument_use := Read |};
          {| argument_name := "l"; argument_use := Read |}]
         ReturnValue [] |}.
(** [fold_right] is a loop from the back, needing no stack. *)
#[export] Instance deque_fold_right_mapping : OperationMapping (Ref (@List.fold_right)) :=
  {| operation_headers := ["deque"];
     operation_cpp := Expr "[](auto _f, auto _a, const auto& _l) { for (auto _it = _l.rbegin(); _it != _l.rend(); ++_it) _a = _f(*_it, _a); return _a; }(%arg(f), %arg(a0), %arg(l))";
     operation_contract :=
       PureOperation
         [{| argument_name := "f"; argument_use := Read |};
          {| argument_name := "a0"; argument_use := Read |};
          {| argument_name := "l"; argument_use := Read |}]
         ReturnValue [] |}.
(** [fold_left] is a loop from the front. *)
#[export] Instance deque_fold_left_mapping : OperationMapping (Ref (@List.fold_left)) :=
  {| operation_headers := ["deque"];
     operation_cpp := Expr "[](auto _f, const auto& _l, auto _a) { for (const auto& _x : _l) _a = _f(_a, _x); return _a; }(%arg(f), %arg(l), %arg(a0))";
     operation_contract :=
       PureOperation
         [{| argument_name := "f"; argument_use := Read |};
          {| argument_name := "l"; argument_use := Read |};
          {| argument_name := "a0"; argument_use := Read |}]
         ReturnValue [] |}.
(** [forallb] stops at the first element [f] rejects. *)
#[export] Instance deque_forallb_mapping : OperationMapping (Ref (@List.forallb)) :=
  {| operation_headers := ["deque"];
     operation_cpp := Expr "[](auto _f, const auto& _l) { for (const auto& _x : _l) if (!_f(_x)) return false; return true; }(%arg(f), %arg(l))";
     operation_contract :=
       PureOperation
         [{| argument_name := "f"; argument_use := Read |};
          {| argument_name := "l"; argument_use := Read |}]
         ReturnValue [] |}.
(** [flat_map f l] appends [f x] for each [x]. *)
#[export] Instance deque_flat_map_mapping : OperationMapping (Ref (@List.flat_map)) :=
  {| operation_headers := ["deque"; "utility"; "type_traits"];
     operation_cpp := Expr "[](auto _f, const auto& _l) { %ret _r; for (const auto& _x : _l) { auto _s = _f(_x); _r.insert(_r.end(), _s.begin(), _s.end()); } return _r; }(%arg(f), %arg(l))";
     operation_contract :=
       PureOperation
         [{| argument_name := "f"; argument_use := Read |};
          {| argument_name := "l"; argument_use := Read |}]
         ReturnValue [] |}.
(** [concat] appends the inner deques in order. *)
#[export] Instance deque_concat_mapping : OperationMapping (Ref (@List.concat)) :=
  {| operation_headers := ["deque"; "type_traits"];
     operation_cpp := Expr "[](const auto& _ls) { %ret _r; for (const auto& _s : _ls) _r.insert(_r.end(), _s.begin(), _s.end()); return _r; }(%arg(l))";
     operation_contract :=
       PureOperation
         [{| argument_name := "l"; argument_use := Read |}]
         ReturnValue [] |}.
(** [list_ascii_of_string] is the string's bytes as a [std::deque<char>]. *)
#[export] Instance deque_list_ascii_of_string_mapping : OperationMapping (Ref (@String.list_ascii_of_string)) :=
  {| operation_headers := ["deque"];
     operation_cpp := Expr "[](const auto& _s) { return std::deque<char>(_s.begin(), _s.end()); }(%arg(s))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s"; argument_use := Read |}]
         ReturnValue [] |}.
(** [string_of_list_ascii] is the bytes gathered into a [std::string]. *)
#[export] Instance deque_string_of_list_ascii_mapping : OperationMapping (Ref (@String.string_of_list_ascii)) :=
  {| operation_headers := ["string"];
     operation_cpp := Expr "[](const auto& _s) { return std::string(_s.begin(), _s.end()); }(%arg(s))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s"; argument_use := Read |}]
         ReturnValue [] |}.

