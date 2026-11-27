(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Typed mappings with an algebraic interface drive extraction: the mapped
    type is the structured canonical type, a constructor is its build
    template, and a match is the constructor views' case tests and
    projections.

    - [Suit]: a three-constructor enumeration mapped to [std::uint8_t].
    - [Maybe A]: an option-like type mapped to
      [std::optional<%stored(element)>], whose component [element] is the
      field of [Just], so its stored type is the one Crane chooses for [A]. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatInt.

Open Scope pstring_scope.

Inductive Suit : Type := Hearts | Spades | Clubs.

Inductive Maybe (A : Type) : Type := Nothing | Just (x : A).
Arguments Nothing {A}.
Arguments Just {A} x.

#[export] Instance suit_mapping : TypeMapping Suit :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Name "std::uint8_t";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews Suit;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref Hearts;
             ctor_build := Expr "std::uint8_t{0}";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 0";
                       case_fields := [] |} |};
          {| ctor_source := Ref Spades;
             ctor_build := Expr "std::uint8_t{1}";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 1";
                       case_fields := [] |} |};
          {| ctor_source := Ref Clubs;
             ctor_build := Expr "std::uint8_t{2}";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 2";
                       case_fields := [] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance maybe_mapping (A : Type) : TypeMapping (Maybe A) :=
  {| type_headers := ["optional"];
     type_cpp :=
       Crane.Cpp.Apply "std::optional"
         [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components :=
       [{| component_name := "element";
           component_type := FieldType (Ref (@Just A)) 0 |}];
     type_copy := CopyComponents ["element"];
     type_access := ReadOnlyValue (ReadByComponents ["element"]);
     type_views := NoViews (Maybe A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@Nothing A);
             ctor_build := Expr "std::optional<%stored(element)>{}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.has_value()";
                       case_fields := [] |} |};
          {| ctor_source := Ref (@Just A);
             ctor_build := Expr "std::optional<%stored(element)>{%a0}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.has_value()";
                       case_fields := [(0, CanonicalBorrowProjection "*%scrut")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

Module TypedMappingAlgebraic.

Definition suit_code (s : Suit) : nat :=
  match s with Hearts => 1 | Spades => 2 | Clubs => 3 end.

Definition next_suit (s : Suit) : Suit :=
  match s with Hearts => Spades | Spades => Clubs | Clubs => Hearts end.

Definition suit_of_code (n : nat) : Maybe Suit :=
  match n with
  | 1 => Just Hearts
  | 2 => Just Spades
  | 3 => Just Clubs
  | _ => Nothing
  end.

Definition maybe_default {A : Type} (m : Maybe A) (d : A) : A :=
  match m with Nothing => d | Just x => x end.

Definition maybe_map {A B : Type} (f : A -> B) (m : Maybe A) : Maybe B :=
  match m with Nothing => Nothing | Just x => Just (f x) end.

Definition code_after (n : nat) : nat :=
  maybe_default (maybe_map (fun s => suit_code (next_suit s)) (suit_of_code n)) 0.

Definition lengths (l : list (Maybe nat)) : nat :=
  fold_left (fun acc m => acc + maybe_default m 0) l 0.

End TypedMappingAlgebraic.

Crane Extraction "typed_mapping_algebraic" TypedMappingAlgebraic.
