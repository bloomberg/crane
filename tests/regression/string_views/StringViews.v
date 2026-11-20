(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Strings as a typed mapping with a [std::string_view] read view
    (docs/typed-mappings-design.md 14.1-14.5, 24.4), from
    [Mapping.StringView]:

    - [size_of] only calls [length]: [std::string_view].
    - [describe] passes its strings to several view-compatible operations
      ([length], [cat], [get], [sub]): [std::string_view] each.
    - [c_size] passes its string to [c_length], a test-only operation that
      needs a NUL-terminated string ([ReadCanonical], [c_str()]):
      [const std::string&].
    - [nonempty_or] observes its string and returns it: the canonical
      string, never a view.
    - [first_two] returns [prefix], a test-only operation whose result is
      a view borrowed from its argument ([ReturnBorrowed ReadViewBorrow]):
      the view escapes as the function's [string] result, so it is
      materialised as a [std::string].  [prefix_size] passes the same
      borrowed view straight to [length], within its owner's lifetime: no
      copy; nor does [joined_prefix_size], whose view is borrowed from a
      temporary [cat] result, which lives to the end of the full
      expression that reads the view.
    - [outer -> size_of]: a read reaches [outer] through [size_of], and a
      temporary [cat] result is passed to [size_of] as a view of the
      temporary, which lives to the end of the call's full expression.
    - A string declared [Write] by an operation mapping is refused: a Rocq
      string is a read-only value. *)

From Stdlib Require Import List.
Import ListNotations.
From Corelib Require Import PrimInt63 PrimString.
From Crane Require Import Mapping.StringView Mapping.Descriptor.
Local Open Scope pstring_scope.

Module StringViews.

  (** A NUL-terminated read: needs the canonical [std::string]. *)
  Axiom c_length : string -> int.

  (** The first [n] characters, as a view of [s]. *)
  Axiom prefix : string -> int -> string.

  Definition size_of (s : string) : int := length s.

  Definition describe (name greeting : string) : string :=
    let whole := cat greeting (cat ", " name) in
    if PrimInt63.ltb (length name) 1 then greeting
    else cat whole (PrimString.sub name 0 1).

  Definition initial (s : string) : char63 := get s 0.

  Definition c_size (s : string) : int := c_length s.

  Definition nonempty_or (s fallback : string) : string :=
    if PrimInt63.eqb (length s) 0 then fallback else s.

  Definition first_two (s : string) : string := prefix s 2.

  Definition prefix_size (s : string) : int := length (prefix s 2).

  (** A view borrowed from a temporary, read within the full expression
      that holds the temporary. *)
  Definition joined_prefix_size (a b : string) : int := length (prefix (cat a b) 3).

  Definition outer (s : string) : int :=
    PrimInt63.add (size_of s) (size_of (cat s s)).

End StringViews.

#[export] Instance c_length_mapping : OperationMapping (Ref StringViews.c_length) :=
  {| operation_headers := ["cstdint"; "cstring"];
     operation_cpp := Expr "static_cast<int64_t>(std::strlen(%arg(s).c_str()))";
     operation_contract :=
       PureOperation [{| argument_name := "s"; argument_use := ReadCanonical |}] ReturnValue [] |}.

#[export] Instance prefix_mapping : OperationMapping (Ref StringViews.prefix) :=
  {| operation_headers := ["string_view"];
     operation_cpp := Expr "%arg(s).substr(0, %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s"; argument_use := Read |};
          {| argument_name := "n"; argument_use := Read |}]
         (ReturnBorrowed ReadViewBorrow {| path_argument := "s"; path_components := [] |})
         [] |}.

Crane Extraction "string_views" StringViews.

(** A Rocq string is a read-only value: an operation cannot write one. *)
Axiom string_poke : string -> int -> string.

Module WriteString.
  #[export] Instance bad : OperationMapping (Ref string_poke) :=
    {| operation_headers := [];
       operation_cpp := Expr "%arg(s)";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "s"; argument_use := Write |};
            {| argument_name := "i"; argument_use := Read |}]
           ReturnValue [] |}.
  Crane Check Mapping string_poke Fails With
    "argument ""s"" is written, but its type's access model is read-only".
End WriteString.
