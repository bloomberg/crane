From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

(** A rose tree whose children are a mapped container with a [Boxed
    Element] wrapper, as ParseALot maps lists: the element is boxed exactly
    where it recurses through the container, so [list rose] is
    [crane::list<crane::box<rose>>] while [list nat] stays unboxed. *)
Module BoxedElementRoseTree.

Inductive rose := Node (n : nat) (kids : list rose).

Fixpoint size (r : rose) : nat :=
  match r with
  | Node _ ks =>
    S ((fix go (l : list rose) : nat :=
          match l with
          | [] => 0
          | k :: t => size k + go t
          end) ks)
  end.

Fixpoint total (r : rose) : nat :=
  match r with
  | Node n ks =>
    n + (fix go (l : list rose) : nat :=
           match l with
           | [] => 0
           | k :: t => total k + go t
           end) ks
  end.

Definition labels (r : rose) : list nat :=
  match r with
  | Node n ks => n :: map (fun k => match k with Node m _ => m end) ks
  end.

Definition sample : rose :=
  Node 1 [Node 2 []; Node 3 [Node 4 []; Node 5 []]; Node 6 []].

Definition sample_size : nat := size sample.
Definition sample_total : nat := total sample.
Definition sample_labels : list nat := labels sample.

End BoxedElementRoseTree.

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
     type_release := OrdinaryRelease;
     type_numerals := None |}.
End ListMapping.

Crane Extraction "boxed_element_rose_tree" BoxedElementRoseTree.
