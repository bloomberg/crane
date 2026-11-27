(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: an inductive with a type mapping, reached
    through a module alias, gets its mapped C++ type but not the rest of its
    mapping.  The type mapping is keyed by the definition (canonical
    identity), so [N.opt] for [Module N := M] is [std::optional<uint64_t>];
    the match template was keyed by the name it was registered under, so a
    match on an [N.opt] is generated as for an ordinary Crane variant --
    [std::holds_alternative<...::No>(o.v())] on a [std::optional]: "no type
    named 'No'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.

Module AliasMappedInductiveMatch.

Module M. Inductive opt := No | Yes : nat -> opt. End M.

Module N := M.

Definition get (o : N.opt) : nat := match o with N.No => 0 | N.Yes n => n end.

Definition result : nat := get (N.Yes 4) + get N.No.

End AliasMappedInductiveMatch.

From Crane Require Mapping.Descriptor.
From Corelib Require PrimString.
From Stdlib Require List.
Module OptMapping.
Import Crane.Mapping.Descriptor PrimString.PStringNotations List.ListNotations.
Local Open Scope pstring_scope.
#[global] Instance opt_mapping : TypeMapping AliasMappedInductiveMatch.M.opt :=
  {| type_headers := ["optional"; "cstdint"];
     type_cpp :=
       Crane.Cpp.Apply "std::optional" [Crane.Cpp.TypeArg (Crane.Cpp.Int Crane.Cpp.U64)];
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews AliasMappedInductiveMatch.M.opt;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref AliasMappedInductiveMatch.M.Yes;
             ctor_build := Expr "std::make_optional<uint64_t>(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation; case_test := "%scrut.has_value()";
                       case_fields := [(0, CanonicalBorrowProjection "*%scrut")] |} |};
          {| ctor_source := Ref AliasMappedInductiveMatch.M.No;
             ctor_build := Expr "std::optional<uint64_t>()";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation; case_test := "!%scrut.has_value()";
                       case_fields := [] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
End OptMapping.
Crane Extraction "alias_mapped_inductive_match" AliasMappedInductiveMatch.
