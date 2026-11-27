(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Standard library extraction for string views ([std::string_view]). *)
From Crane Require Extraction.
From Crane Require Export External.StringViewDefs.

From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[export] Instance string_view_mapping : TypeMapping string_view :=
  value_type ["string_view"] (Name "std::basic_string_view<char>") UnknownCopy.
#[export] Instance empty_mapping : OperationMapping (Ref empty) :=
  pure ["string_view"] ["sv"] (Method (Arg "sv") "empty" []).
#[export] Instance sv_eq_mapping : OperationMapping (Ref sv_eq) :=
  pure ["string_view"] ["a"; "b"] (Binop Equal (Arg "a") (Arg "b")).
#[export] Instance length_mapping : OperationMapping (Ref length) :=
  pure ["string_view"] ["sv"] (Method (Arg "sv") "length" []).
(* [length_substr]/[length_substr_prefix] (StringViewDefs.v) define [substr]
   as total: a [start] at or past the view's length yields an empty view
   rather than raising, and [len] is clamped to what remains.
   [std::basic_string_view::substr] already clamps [count], but throws when
   [pos > size()]. The guard reproduces the axiomatized clamp-to-empty
   behavior instead of letting the exception escape and terminate the
   generated program (CWE-248/CWE-755). *)
#[export] Instance substr_mapping : OperationMapping (Ref substr) :=
  pure ["string_view"; "cstdint"] ["sv"; "start"; "len"]
    (Cond (Binop And (Binop GreaterEq (Arg "start") (lit 0))
             (Binop LessEq (Arg "start") (exact I64 (Method (Arg "sv") "length" []))))
       (Method (Arg "sv") "substr" [Arg "start"; Arg "len"])
       (Build (Name "std::basic_string_view<char>") [])).
#[export] Instance sv_of_string_mapping : OperationMapping (Ref sv_of_string) :=
  {| operation_headers := ["string_view"];
     operation_cpp := Expr "{%arg(s).data(), %arg(s).size()}";
     operation_contract := PureOperation (uses ReadCanonical ["s"]) ReturnValue [] |}.
#[export] Instance contains_mapping : OperationMapping (Ref contains) :=
  pure ["string_view"] ["sv"; "c"] (Method (Arg "sv") "contains" [wrap Char (Arg "c")]).
(* The [sv_get] axioms (StringViewDefs.v) constrain only in-range indices, so
   returning the null char for an out-of-range index is consistent with the
   specification and makes the operation total. The bounds check prevents an
   out-of-bounds read of a possibly non-owning string view (CWE-125).
   Use [sv_at] when a throwing, checked accessor is desired instead. *)
#[export] Instance sv_get_mapping : OperationMapping (Ref sv_get) :=
  pure ["string_view"; "cstdint"] ["sv"; "i"]
    (Cond (Binop And (Binop GreaterEq (Arg "i") (lit 0))
             (Binop Less (Arg "i") (exact I64 (Method (Arg "sv") "length" []))))
       (exact I64 (wrap UChar (Index (Arg "sv") (Arg "i"))))
       (IntLit I64 0)).
#[export] Instance sv_at_mapping : OperationMapping (Ref sv_at) :=
  pure ["string_view"; "cstdint"] ["sv"; "i"] (exact I64 (wrap UChar (Method (Arg "sv") "at" [Arg "i"]))).
#[export] Instance empty_sv_mapping : OperationMapping (Ref empty_sv) :=
  pure ["string_view"] [] (Build (Name "std::string_view") [Verbatim "nullptr"; lit 0]).
