(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A sequence mapped to [crane::shared_array], as ParseALot maps its DFA
    tables: built from a list, nested, indexed, matched on, extended at the
    front, and copied into a list, whose copies share the arrays. *)

From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.

Module SharedArrayVec.

Inductive vec (X : Type) : Type :=
| vnil : vec X
| vcons : X -> vec X -> vec X.

Arguments vnil {X}.
Arguments vcons {X} _ _.

Fixpoint vec_of_list {X} (l : list X) : vec X :=
  match l with [] => vnil | h :: t => vcons h (vec_of_list t) end.

Fixpoint vec_nth {X} (v : vec X) (n : nat) (d : X) : X :=
  match v, n with
  | vnil, _ => d
  | vcons h _, O => h
  | vcons _ t, S m => vec_nth t m d
  end.

Fixpoint vec_sum (v : vec nat) : nat :=
  match v with vnil => 0 | vcons h t => h + vec_sum t end.

Definition table : vec (vec nat) :=
  vec_of_list (map vec_of_list [[1; 2; 3]; [4; 5]; []; [6]]).

Definition copies : list (vec (vec nat)) := [table; table; vcons (vec_of_list [7]) table].

Definition result : nat :=
  vec_nth (vec_nth table 1 vnil) 1 0                          (* 5 *)
  + vec_nth (vec_nth table 2 vnil) 0 100                      (* 100 *)
  + vec_sum (vec_nth table 0 vnil)                            (* 6 *)
  + fold_left (fun acc t => acc + vec_sum (vec_nth t 0 vnil)) copies 0. (* 6+6+7 *)

End SharedArrayVec.

(* Lists as [crane::list], as ParseALot's ConsList.v has them: an array is
   built from one by walking it. *)
Module ListMapping.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance list_mapping (A : Type) : TypeMapping (list A) :=
  {| type_headers := ["conslist.h"];
     type_cpp := Crane.Cpp.Apply "crane::list" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
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
Module VecMapping.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance vec_mapping (A : Type) : TypeMapping (SharedArrayVec.vec A) :=
  {| type_headers := ["shared_array.h"];
     type_cpp := Crane.Cpp.Apply "crane::shared_array" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components :=
       [{| component_name := "element"; component_type := FieldType (Ref (@SharedArrayVec.vcons A)) 0 |}];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (SharedArrayVec.vec A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@SharedArrayVec.vnil A);
             ctor_build := Expr "crane::shared_array<%stored(element)>{}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.empty()"; case_fields := [] |} |};
          {| ctor_source := Ref (@SharedArrayVec.vcons A);
             ctor_build := Expr "%a1.push_front(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.empty()";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "%scrut.front()");
                          (1, OwnedProjection "%scrut.drop(1)")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
End VecMapping.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance vec_of_list_mapping : OperationMapping (Ref (@SharedArrayVec.vec_of_list)) :=
  pure_cpp ["shared_array.h"] ["l"]
    (Expr "crane::shared_array<%t0>::of_range(%arg(l))").
Crane Extraction "shared_array_vec" SharedArrayVec.
