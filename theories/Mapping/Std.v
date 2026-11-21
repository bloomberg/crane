(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Standard-library extraction mappings: [StdCore] ([option], [prod],
    [int63], [float], [char63]) and Rocq's primitive [string] as a
    [std::string] with a [std::string_view] read view
    (docs/typed-mappings-design.md 14.1-14.5).  Every mapping is typed and
    activates on [Import].

    A Rocq string is an immutable value, so it has a read view and no
    writable view, and no operation may write it:
    - a generated function that only reads a string -- passes it to
      [length], [get], [sub], or to a function that only reads it -- takes
      a [std::string_view];
    - one that keeps, returns, stores or matches it, or passes it to an
      operation that reads it canonically ([cat], or [ReadCanonical] for
      [c_str()]) or to a legacy mapping, takes [const std::string&]
      ([std::string] when it owns it);
    - a function returning a string returns a [std::string].
    A view an operation returns borrowed ([ReturnBorrowed ReadViewBorrow])
    is materialised as a [std::string] where it escapes its owner.

    Sets the stdlib flavor to ["std"]. *)
From Crane Require Extraction.
From Crane Require Export Mapping.StdCore.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

#[export] Instance std_string_mapping : TypeMapping PrimString.string :=
  {| type_headers := ["string"; "string_view"];
     type_cpp := Crane.Cpp.Name "std::string";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views :=
       ReadViews
         {| view_headers := ["string_view"];
            view_cpp := Crane.Cpp.Name "std::string_view";
            view_from_canonical := "std::string_view{%value}";
            view_escape := MaterialiseView (Expr "std::string{%view}") |};
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance string_length_mapping : OperationMapping (Ref PrimString.length) :=
  {| operation_headers := ["cstdint"; "string_view"];
     operation_cpp := Expr "static_cast<int64_t>(%arg(s).size())";
     operation_contract :=
       PureOperation [{| argument_name := "s"; argument_use := Read |}] ReturnValue [] |}.

(** [cat] reads both strings canonically and is spelled as [+], so that a
    chain of concatenations appends to one growing temporary, as C++
    evaluates [a + b + c]; through views each link would allocate a string
    of its own.  The result is cut to [max_length] bytes, as Rocq's is;
    [crane::string_capped] moves the temporary through. *)
#[export] Instance string_cat_mapping : OperationMapping (Ref PrimString.cat) :=
  {| operation_headers := ["string"; "crane_string.h"];
     operation_cpp := Expr "crane::string_capped(%arg(s1) + %arg(s2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s1"; argument_use := ReadCanonical |};
          {| argument_name := "s2"; argument_use := ReadCanonical |}]
         ReturnValue [] |}.

(** Total, as Rocq's: an index out of range reads the null character. *)
#[export] Instance string_get_mapping : OperationMapping (Ref PrimString.get) :=
  {| operation_headers := ["crane_string.h"];
     operation_cpp := Expr "crane::string_get(%arg(s), %arg(i))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s"; argument_use := Read |};
          {| argument_name := "i"; argument_use := Read |}]
         ReturnValue [] |}.

(** Total, as Rocq's: the length is clamped to [max_length] and the
    character to its low byte. *)
#[export] Instance string_make_mapping : OperationMapping (Ref PrimString.make) :=
  {| operation_headers := ["crane_string.h"];
     operation_cpp := Expr "crane::string_make(%arg(n), %arg(c))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "c"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance string_max_length_mapping : OperationMapping (Ref PrimString.max_length) :=
  {| operation_headers := ["crane_string.h"];
     operation_cpp := Expr "crane::string_max_length";
     operation_contract := PureOperation [] ReturnValue [] |}.

(** Lexicographic on the bytes read unsigned, as Rocq's.  The result is
    the [comparison] enum, whose constructors are numbered in declaration
    order ([Eq], [Lt], [Gt]); [%ret] names it. *)
#[export] Instance string_compare_mapping : OperationMapping (Ref PrimString.compare) :=
  {| operation_headers := ["crane_string.h"];
     operation_cpp := Expr "static_cast<%ret>(crane::string_compare(%arg(s1), %arg(s2)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s1"; argument_use := Read |};
          {| argument_name := "s2"; argument_use := Read |}]
         ReturnValue [] |}.

(** Total, as Rocq's; returns an owner (design 14.4), though it reads its
    argument through a view. *)
#[export] Instance string_sub_mapping : OperationMapping (Ref PrimString.sub) :=
  {| operation_headers := ["crane_string.h"];
     operation_cpp := Expr "crane::string_sub(%arg(s), %arg(off), %arg(len))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s"; argument_use := Read |};
          {| argument_name := "off"; argument_use := Read |};
          {| argument_name := "len"; argument_use := Read |}]
         ReturnValue [] |}.
