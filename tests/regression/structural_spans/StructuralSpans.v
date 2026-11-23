(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Spans over a structural buffer.  [Buf A] is a test-only mapping of a
    mutable buffer: a [std::vector<A>] with a read view [std::span<const A>]
    (materialised by copying the elements) and a writable view [std::span<A>]
    (borrow-only):

    - [total] only reads: [std::span<const T>].
    - [bump] reads and writes an element: [std::span<T>].
    - [grow] writes an element and calls [buf_resize], which may reallocate
      ([WriteCanonical], [InvalidatesViews]): not a span, the buffer by
      reference, [std::vector<T>&].
    - [window_total] passes a subspan ([buf_window], a view borrowed from
      its argument) straight to [buf_total]: no copy.
    - [window] returns the subspan as a [Buf]: it escapes its owner, and is
      materialised as a [std::vector].
    - [fresh_window_total] takes a subspan of a temporary buffer, bound
      ahead of the call that reads it twice: the temporary is bound ahead
      of it, so that it outlives the view.
    - [self_append] appends a buffer to itself: [buf_append] reads [src]
      through a view and resizes [dst], so the view of the same buffer
      would dangle; Crane passes a view of a copy instead.
    - [Ring A] has a borrow-only read view: a subrange of one escaping its
      owner is refused at extraction. *)

From Stdlib Require Import List.
From ITree Require Import ITree Events.Exception.
From Crane Require Import
  Mapping.NatIntStd
  Monads.ITree
  Monads.Error
  Mapping.Descriptor.
Import ListNotations.
From Corelib Require Import PrimString.
Import Monads.
Local Open Scope monad_scope.
Local Open Scope pstring_scope.

Axiom Buf : Type -> Type.
Axiom buf_make : forall {A : Type}, nat -> A -> Buf A.
Axiom buf_get : forall {A : Type}, Buf A -> nat -> itree (exceptE Err) A.
Axiom buf_set : forall {A : Type}, Buf A -> nat -> A -> itree (exceptE Err) unit.
Axiom buf_resize : forall {A : Type}, Buf A -> nat -> A -> itree (exceptE Err) unit.
Axiom buf_append : forall {A : Type}, Buf A -> Buf A -> itree (exceptE Err) unit.
Axiom buf_window : forall {A : Type}, Buf A -> nat -> nat -> Buf A.
Axiom buf_total : forall {A : Type}, Buf A -> A.
Axiom buf_elems : forall {A : Type}, Buf A -> list A.

#[export] Instance buf_mapping (A : Type) : TypeMapping (Buf A) :=
  {| type_headers := ["vector"];
     type_cpp :=
       Crane.Cpp.Apply "std::vector" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components := [{| component_name := "element"; component_type := KnownType A |}];
     type_copy := DuplicateValue;
     type_access := MutableValue ReadByConstReference;
     type_views :=
       ReadWriteViews
         {| view_headers := ["span"];
            view_cpp :=
              Crane.Cpp.Apply "std::span"
                [Crane.Cpp.TypeArg (Crane.Cpp.Const (Crane.Cpp.StoredComponent "element"))];
            view_from_canonical := "std::span<const %stored(element)>{%value}";
            view_escape := MaterialiseView (Expr "std::vector<%stored(element)>(%view.begin(), %view.end())") |}
         {| view_headers := ["span"];
            view_cpp :=
              Crane.Cpp.Apply "std::span" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
            view_from_canonical := "std::span<%stored(element)>{%value}";
            view_escape := BorrowOnly |}
         "std::span<const %stored(element)>{%view}";
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance buf_make_mapping : OperationMapping (Ref (@buf_make)) :=
  {| operation_headers := ["vector"];
     operation_cpp := Expr "std::vector<%stored(element)>(%arg(n), %arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance buf_get_mapping : OperationMapping (Ref (@buf_get)) :=
  {| operation_headers := ["span"];
     operation_cpp := Expr "%arg(b)[%arg(i)]";
     operation_contract :=
       PureOperation
         [{| argument_name := "b"; argument_use := Read |};
          {| argument_name := "i"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "b"; path_components := ["element"] |}] |}.

#[export] Instance buf_set_mapping : OperationMapping (Ref (@buf_set)) :=
  {| operation_headers := ["span"];
     operation_cpp := Expr "%arg(b)[%arg(i)] = %arg(x)";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "b"; argument_use := Write |};
          {| argument_name := "i"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Take |}]
         ReturnValue
         [WritesComponent {| path_argument := "b"; path_components := ["element"] |} (Some "x");
          InvalidatesElementBorrows {| path_argument := "b"; path_components := ["element"] |}] |}.

(** May reallocate: canonical, and invalidates views. *)
#[export] Instance buf_resize_mapping : OperationMapping (Ref (@buf_resize)) :=
  {| operation_headers := ["vector"];
     operation_cpp := Expr "%arg(b).resize(%arg(n), %arg(x))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "b"; argument_use := WriteCanonical |};
          {| argument_name := "n"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Read |}]
         ReturnValue
         [WritesComponent {| path_argument := "b"; path_components := ["element"] |} None;
          InvalidatesViews {| path_argument := "b"; path_components := ["element"] |}] |}.

#[export] Instance buf_append_mapping : OperationMapping (Ref (@buf_append)) :=
  {| operation_headers := ["vector"];
     operation_cpp := Expr "%arg(dst).insert(%arg(dst).end(), %arg(src).begin(), %arg(src).end())";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "dst"; argument_use := WriteCanonical |};
          {| argument_name := "src"; argument_use := Read |}]
         ReturnValue
         [WritesComponent {| path_argument := "dst"; path_components := ["element"] |} None;
          InvalidatesViews {| path_argument := "dst"; path_components := ["element"] |}] |}.

(** A subrange of [b], borrowed from it. *)
#[export] Instance buf_window_mapping : OperationMapping (Ref (@buf_window)) :=
  {| operation_headers := ["span"];
     operation_cpp := Expr "%arg(b).subspan(%arg(off), %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "b"; argument_use := Read |};
          {| argument_name := "off"; argument_use := Read |};
          {| argument_name := "n"; argument_use := Read |}]
         (ReturnBorrowed ReadViewBorrow {| path_argument := "b"; path_components := [] |})
         [] |}.

#[export] Instance buf_total_mapping : OperationMapping (Ref (@buf_total)) :=
  {| operation_headers := ["numeric"];
     operation_cpp := Expr "std::accumulate(%arg(b).begin(), %arg(b).end(), %stored(element){})";
     operation_contract :=
       PureOperation [{| argument_name := "b"; argument_use := Read |}] ReturnValue [] |}.

#[export] Instance buf_elems_mapping : OperationMapping (Ref (@buf_elems)) :=
  {| operation_headers := ["crane_st.h"];
     operation_cpp := Expr "crane::st::elems<List<%stored(element)>>(%arg(b))";
     operation_contract :=
       PureOperation [{| argument_name := "b"; argument_use := Read |}] ReturnValue [] |}.

Module StructuralSpans.

  Notation E := (exceptE Err).

  Definition total (b : Buf nat) : nat := buf_total b.

  Definition bump (b : Buf nat) (i : nat) : itree E unit :=
    x <- buf_get b i;;
    buf_set b i (S x).

  Definition grow (b : Buf nat) (n : nat) : itree E unit :=
    buf_set b 0 7;;
    buf_resize b n 1.

  Definition window_total (b : Buf nat) : nat := buf_total (buf_window b 1 2).

  Definition window (b : Buf nat) : Buf nat := buf_window b 1 2.

  (** A subspan of a temporary buffer, bound ahead of [buf_total] (which
      places its argument twice): the temporary is bound ahead too, so
      that it outlives the view. *)
  Definition fresh_window_total (n : nat) : nat := buf_total (buf_window (buf_make n 3) 1 2).

  Definition self_append (b : Buf nat) : itree E unit := buf_append b b.

  (** Runs a computation; extracted as the identity. *)
  Axiom run : forall (A : Type), itree E A -> A.

  Definition scenario (n : nat) : list nat * nat * nat * list nat :=
    run (list nat * nat * nat * list nat)
      (let b := buf_make 3 1 in
       bump b 1;;
       grow b n;;
       self_append b;;
       Ret (buf_elems b, total b, window_total b, buf_elems (window b))).

End StructuralSpans.

Crane Extract Inlined Constant StructuralSpans.run => "%a0".

Crane Extraction "structural_spans" StructuralSpans.

(** A ring buffer whose read view may not be copied. *)
Axiom Ring : Type -> Type.
Axiom ring_window : forall {A : Type}, Ring A -> nat -> Ring A.

Module RingMapping.
  #[export] Instance ring_mapping (A : Type) : TypeMapping (Ring A) :=
    {| type_headers := ["vector"];
       type_cpp :=
         Crane.Cpp.Apply "std::vector" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
       type_components := [{| component_name := "element"; component_type := KnownType A |}];
       type_copy := DuplicateValue;
       type_access := ReadOnlyValue ReadByConstReference;
       type_views :=
         ReadViews
           {| view_headers := ["span"];
              view_cpp :=
                Crane.Cpp.Apply "std::span"
                  [Crane.Cpp.TypeArg (Crane.Cpp.Const (Crane.Cpp.StoredComponent "element"))];
              view_from_canonical := "std::span<const %stored(element)>{%value}";
              view_escape := BorrowOnly |};
       type_interface := AbstractInterface;
       type_model := Identity;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.

  #[export] Instance ring_window_mapping : OperationMapping (Ref (@ring_window)) :=
    {| operation_headers := ["span"];
       operation_cpp := Expr "%arg(r).subspan(%arg(off))";
       operation_contract :=
         PureOperation
           [{| argument_name := "r"; argument_use := Read |};
            {| argument_name := "off"; argument_use := Read |}]
           (ReturnBorrowed ReadViewBorrow {| path_argument := "r"; path_components := [] |})
           [] |}.
End RingMapping.

Import RingMapping.

Module RingEscape.
  Definition tail_of (r : Ring nat) : Ring nat := ring_window r 1.
End RingEscape.
Fail Crane Extraction "structural_spans_ring_escape" RingEscape.

(** An operation that may reallocate cannot work through a view. *)
Axiom buf_shrink : forall {A : Type}, Buf A -> nat -> itree (exceptE Err) unit.

Module ResizeThroughView.
  #[export] Instance bad : OperationMapping (Ref (@buf_shrink)) :=
    {| operation_headers := [];
       operation_cpp := Expr "%arg(b).resize(%arg(n))";
       operation_contract :=
         EffectfulOperation
           [{| argument_name := "b"; argument_use := Write |};
            {| argument_name := "n"; argument_use := Read |}]
           ReturnValue
           [InvalidatesViews {| path_argument := "b"; path_components := ["element"] |}] |}.
  Crane Check Mapping (@buf_shrink nat) Fails With
    "argument ""b"" is declared Write, so it is given as its type's writable view, but InvalidatesViews names it".
End ResizeThroughView.
