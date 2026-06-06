(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Regression test for any_cast<std::any> in pair destructuring when
   fix_a_fired applies.

   symbols_semty is a dependent type family that erases to std::any.
   SemVal is an axiom type that also erases to std::any.  When
   destructuring a pair from symbols_semty, bound variables of type
   SemVal must NOT get any_cast<std::any> — they should pass through
   directly since the value IS already std::any. *)

From Crane Require Import Mapping.NatIntStd.
Require Import Coq.Lists.List.
Import ListNotations.
Require Crane.Extraction.

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

Crane Extract Inlined Constant AnyCastNestedPair.mkSemVal => "std::any(%a0)".
Crane Extract Inlined Constant AnyCastNestedPair.getSemVal => "std::any_cast<uint64_t>(%a0)".

Crane Extraction "any_cast_nested_pair" AnyCastNestedPair.
