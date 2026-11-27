From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

(** A rose tree over a container with a [Boxed Element] wrapper and a
    [Drain] clause, as ParseALot's ConsList.v maps lists: the destructor
    takes a deep tree apart through the drain rather than by recursion. *)
Module BoxedElementDrain.

Inductive rose := Node (n : nat) (kids : list rose).

Fixpoint total (r : rose) : nat :=
  match r with
  | Node n ks =>
    n + (fix go (l : list rose) : nat :=
           match l with
           | [] => 0
           | k :: t => total k + go t
           end) ks
  end.

Fixpoint spine (d : nat) : rose :=
  match d with
  | 0 => Node 1 []
  | S d' => Node 1 [spine d']
  end.

Definition sample : rose := Node 2 [Node 3 []; Node 4 [Node 5 []]].

Definition sample_total : nat := total sample.

End BoxedElementDrain.

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

Crane Extraction "boxed_element_drain" BoxedElementDrain.
