From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

(** A module type naming a mapped container of an element that recurses
    through it, under a [BoxedComponent] box: the module's struct holds
    [crane::list<crane::box<rose>>], so the concept the module type becomes
    has to ask for that type too, the element hole decided as everywhere
    else, or the module satisfying the module type does not satisfy the
    concept: [children]'s result is asked for by [std::same_as]. *)
Module BoxedElementConcept.

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

Module Type FOREST.
  Parameter forest : list rose.
  Parameter count : list rose -> nat.
  Parameter children : rose -> list rose.
End FOREST.

Module Forest <: FOREST.
  Definition forest : list rose := [Node 1 []; Node 2 [Node 3 []]].
  Definition count (l : list rose) : nat := fold_left (fun n r => n + size r) l 0.
  Definition children (r : rose) : list rose := match r with Node _ ks => ks end.
End Forest.

Module Measure (F : FOREST).
  Definition total : nat := F.count F.forest + F.count (flat_map F.children F.forest).
End Measure.

Module M := Measure Forest.

Definition total : nat := M.total.

End BoxedElementConcept.

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

Crane Extraction "boxed_element_concept" BoxedElementConcept.
