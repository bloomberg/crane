(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Regression test for any_cast<std::any> in pair destructuring when
   fix_a_fired applies.

   symbols_semty is a dependent type family that erases to std::any.
   SemVal is an axiom type that also erases to std::any.  When
   destructuring a pair from symbols_semty, bound variables of type
   SemVal must NOT get any_cast<std::any> — they should pass through
   directly since the value IS already std::any. *)

From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Crane.Extraction.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

Module AnyCastNestedPair.

Axiom SemVal : Type.
Axiom mkSemVal : nat -> SemVal.
Axiom getSemVal : SemVal -> nat.

Fixpoint symbols_semty (gamma : list nat) : Type :=
  match gamma with
  | nil => unit
  | cons _ rest => (SemVal * symbols_semty rest)%type
  end.

Definition apply_pred (input : symbols_semty [1; 2]) : nat :=
  let '(v1, rest) := input in
  let '(v2, _) := rest in
  getSemVal v1 + getSemVal v2.

Definition test_pred (a b : nat) : nat :=
  apply_pred (mkSemVal a, (mkSemVal b, tt)).

End AnyCastNestedPair.

#[global] Instance mkSemVal_mapping : OperationMapping (Ref (@AnyCastNestedPair.mkSemVal)) :=
  pure_cpp [] ["x0"]
    (Structured (Call "crane::obj" [] [Arg "x0"])).
#[global] Instance getSemVal_mapping : OperationMapping (Ref (@AnyCastNestedPair.getSemVal)) :=
  pure_cpp [] ["x0"]
    (Expr "crane::any_cast<uint64_t>(%arg(x0))").

Crane Extraction "any_cast_nested_pair" AnyCastNestedPair.
