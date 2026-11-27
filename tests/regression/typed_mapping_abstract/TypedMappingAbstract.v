(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Typed mappings with an abstract interface, and the diagnostics of
    using a mapped type the way its mapping forbids.

    - [Counter]: an axiomatised type mapped to [std::int64_t] with
      [AbstractInterface], used only through legacy inline constants
      (operation mappings come later): the type side is the typed mapping.
    - [Token]: an inductive mapped abstractly.  Matching on it, or building
      it, in source is refused.
    - [Bead]: given a legacy [Crane Extract Numeral] and a typed mapping,
      which is refused.
    - [Pin]: mapped both by [Crane Extract Inductive] and by a typed
      mapping, which is refused. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatInt.

Open Scope pstring_scope.

Axiom Counter : Type.
Axiom counter_zero : Counter.
Axiom counter_tick : Counter -> Counter.
Axiom counter_value : Counter -> nat.

Crane Extract Inlined Constant counter_zero => "std::int64_t{0}".
Crane Extract Inlined Constant counter_tick => "(%a0 + 1)".
Crane Extract Inlined Constant counter_value => "static_cast<uint64_t>(%a0)".

#[export] Instance counter_mapping : TypeMapping Counter :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Name "std::int64_t";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews Counter;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

Inductive Token : Type := token (serial : nat).

#[export] Instance token_mapping : TypeMapping Token :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Name "std::uint32_t";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews Token;
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

Module TypedMappingAbstract.

Fixpoint ticks (n : nat) (c : Counter) : Counter :=
  match n with
  | 0 => c
  | S m => ticks m (counter_tick c)
  end.

Definition count_to (n : nat) : nat := counter_value (ticks n counter_zero).

Definition later (c : Counter) : Counter := counter_tick (counter_tick c).

End TypedMappingAbstract.

Crane Extraction "typed_mapping_abstract" TypedMappingAbstract.

(** Matching on an abstract mapped type is refused. *)
Module AbstractMatch.
Definition serial (t : Token) : nat := match t with token n => n end.
End AbstractMatch.
Fail Crane Extraction "typed_mapping_abstract_match" AbstractMatch.

(** So is building one. *)
Module AbstractBuild.
Definition first_token : Token := token 1.
End AbstractBuild.
Fail Crane Extraction "typed_mapping_abstract_build" AbstractBuild.

(** A legacy [Crane Extract Numeral] on a typed head is refused too:
    a typed type's literals are its descriptor's.  The
    instance is imported only inside the module that extracts, so this
    conflict is the only one active there. *)
Inductive Bead : Type := bead_zero | bead_next (b : Bead).
Crane Extract Numeral Bead => "%nu".

Module BeadMapping.
  #[export] Instance bead_mapping : TypeMapping Bead :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "unsigned";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Bead;
       type_interface := AbstractInterface;
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
End BeadMapping.

Module UsesBead.
  Import BeadMapping.
  Definition keep (b : Bead) : Bead := b.
  Fail Crane Extraction "typed_mapping_abstract_numeral_conflict" keep.
End UsesBead.

(** A type mapped both by a legacy command and by a typed mapping. *)
Inductive Pin : Type := pin.
Crane Extract Inductive Pin => "int" [ "0" ] "%br0".

Module PinMapping.
  #[export] Instance pin_mapping : TypeMapping Pin :=
    {| type_headers := [];
       type_cpp := Crane.Cpp.Name "int";
       type_components := [];
       type_copy := BitCopy;
       type_access := ReadOnlyValue ReadByValue;
       type_views := NoViews Pin;
       type_interface :=
         AlgebraicInterface
           [{| ctor_source := Ref pin; ctor_build := Expr "0"; ctor_view := None |}];
       type_model := Structural;
       type_lifetime := NativeRAII;
       type_release := OrdinaryRelease;
       type_numerals := None |}.
End PinMapping.

Module UsesPin.
Definition the_pin : Pin := pin.
End UsesPin.

(* With both mappings active, extraction is refused. *)
Import PinMapping.
Fail Crane Extraction "typed_mapping_abstract_pin_conflict" UsesPin.
