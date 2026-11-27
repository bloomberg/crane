(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A raw-pointer array mapping, for tests only: [RawArray A] is a
    [std::vector<A>*] that a region owns, a mutable handle passed by value.

    - Reading or writing through it takes the pointer by value, at every
      level of a chain of calls ending in the write: copying a pointer is
      cheaper than referring to it, and writing the vector does not reseat
      the pointer.
    - Reseating it ([Replace]) takes [std::vector<A>*&].
    - A raw pointer owns nothing: [NativeRAII] is refused, and [RegionOwned],
      [ExternallyOwned] and [ManualShared] are accepted. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatInt.

Open Scope pstring_scope.

Definition support : string := "typed_mapping_raw_array_support.h".

Axiom RawArray : Type -> Type.
Axiom raw_make : forall {A : Type}, nat -> A -> RawArray A.
Axiom raw_get : forall {A : Type} (a : RawArray A) (i : nat), A.
Axiom raw_set : forall {A : Type} (a : RawArray A) (i : nat) (x : A), RawArray A.
Axiom raw_reseat : forall {A : Type} (a : RawArray A) (n : nat), RawArray A.

(** The region that owns every raw array. *)
Axiom raw_region : unit.

#[export] Instance raw_array_mapping (A : Type) : TypeMapping (RawArray A) :=
  {| type_headers := [support];
     type_cpp :=
       Crane.Cpp.Pointer
         (Crane.Cpp.Apply "std::vector"
            [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")]);
     type_components := [{| component_name := "contents"; component_type := KnownType A |}];
     type_copy := BitCopy;
     type_access := MutableHandle HandleByValue;
     type_views := NoViews (RawArray A);
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := RegionOwned (Ref raw_region);
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance raw_make_mapping (A : Type) : OperationMapping (Ref (@raw_make A)) :=
  {| operation_headers := [support];
     operation_cpp := Expr "raw_support::make<%stored(contents)>(%arg(n), %arg(x))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Read |}]
         (ReturnFreshIdentity []) [] |}.

#[export] Instance raw_get_mapping (A : Type) : OperationMapping (Ref (@raw_get A)) :=
  {| operation_headers := [];
     operation_cpp := Expr "(*%arg(a))[%arg(i)]";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "i"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance raw_set_mapping (A : Type) : OperationMapping (Ref (@raw_set A)) :=
  {| operation_headers := [support];
     operation_cpp := Expr "raw_support::set(%arg(a), %arg(i), %arg(x))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "a"; argument_use := Write |};
          {| argument_name := "i"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Read |}]
         (ReturnSameIdentity "a") [] |}.

#[export] Instance raw_reseat_mapping (A : Type) : OperationMapping (Ref (@raw_reseat A)) :=
  {| operation_headers := [support];
     operation_cpp := Expr "raw_support::reseat(%arg(a), %arg(n))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "a"; argument_use := Replace |};
          {| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.

(** The lifetime models a raw pointer may have. *)
Axiom ExternalArray ManualArray BadArray : Type.
Axiom manual_retain manual_release : unit.

#[export] Instance external_array_mapping : TypeMapping ExternalArray :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Pointer (Crane.Cpp.Apply "std::vector" [Crane.Cpp.TypeArg (Crane.Cpp.Name "int")]);
     type_components := [];
     type_copy := BitCopy;
     type_access := MutableHandle HandleByValue;
     type_views := NoViews ExternalArray;
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := ExternallyOwned;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance manual_array_mapping : TypeMapping ManualArray :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Pointer (Crane.Cpp.Apply "std::vector" [Crane.Cpp.TypeArg (Crane.Cpp.Name "int")]);
     type_components := [];
     type_copy := BitCopy;
     type_access := MutableHandle HandleByValue;
     type_views := NoViews ManualArray;
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := ManualShared (Ref manual_retain) (Ref manual_release);
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance bad_array_mapping : TypeMapping BadArray :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Pointer (Crane.Cpp.Apply "std::vector" [Crane.Cpp.TypeArg (Crane.Cpp.Name "int")]);
     type_components := [];
     type_copy := BitCopy;
     type_access := MutableHandle HandleByValue;
     type_views := NoViews BadArray;
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

Crane Check Mapping (RawArray nat) Selects raw_array_mapping.
Crane Check Mapping ExternalArray Selects external_array_mapping.
Crane Check Mapping ManualArray Selects manual_array_mapping.
Crane Check Mapping BadArray Fails With
  "the canonical type is a raw pointer, which owns nothing, but the lifetime model is NativeRAII".

Module TypedMappingRawArray.

(** Reads: the pointer by value. *)
Definition get_cell (a : RawArray nat) (i : nat) : nat := raw_get a i.

(** Writes through the pointer, two calls deep: by value at each level. *)
Definition set_cell (a : RawArray nat) (i : nat) (x : nat) : RawArray nat := raw_set a i x.
Definition set_middle (a : RawArray nat) (i : nat) : RawArray nat := set_cell a i (S i).
Definition set_outer (a : RawArray nat) : nat := get_cell (set_middle a 1) 1.

(** Reseats the pointer: [std::vector<A>*&]. *)
Definition reseat_cell (a : RawArray nat) (n : nat) : nat := raw_get (raw_reseat a n) 0.

(** A [bool] array, read and written. *)
Definition flip_cell (a : RawArray bool) (i : nat) : bool :=
  raw_get (raw_set a i (negb (raw_get a i))) i.

Definition run_nat (n : nat) : nat * nat :=
  let a := raw_make n 0 in
  let w := set_outer a in
  (w, reseat_cell a 5).

Definition run_bool (n : nat) : bool := flip_cell (raw_make n false) 0.

End TypedMappingRawArray.

Crane Extraction "typed_mapping_raw_array" TypedMappingRawArray.
