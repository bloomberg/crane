(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Regression test for any_cast<std::any> in pair destructuring when
   fix_a_fired applies.

   The grammar framework pattern:
   - A function receives a value of type symbols_semty (erased to std::any)
   - It pattern matches it as a pair
   - fix_a_fired triggers (scrutinee is erased)
   - Bound variables get any_cast<T> for their declared type T
   - When T is a ConstRef that renders as std::any, this produces
     any_cast<std::any>(v) which throws bad_any_cast

   This test uses a dependent type family (symbols_semty) with an
   abstract type (SemVal) to reproduce the pattern. *)

From Crane Require Import Mapping.NatIntStd.
Require Import Coq.Lists.List.
Import ListNotations.
Require Crane.Extraction.

Module AnyCastNestedPair.

(* Abstract semantic value type — stays as ConstRef in extraction *)
Axiom SemVal : Type.
Axiom mkSemVal : nat -> SemVal.
Axiom getSemVal : SemVal -> nat.

(* Compute the product type for a list of symbols.
   symbols_semty [1;2] = SemVal * (SemVal * unit)
   This is a type family that can't be statically resolved,
   so it erases to std::any in C++. *)
Fixpoint symbols_semty (gamma : list nat) : Type :=
  match gamma with
  | nil => unit
  | cons _ rest => (SemVal * symbols_semty rest)%type
  end.

(* A predicate that receives the erased tuple and destructures it.
   The parameter has type symbols_semty [...] which erases to std::any.
   The pair match triggers fix_a_fired.  The bound variable of type
   SemVal (ConstRef) should NOT get any_cast<std::any> — it should
   be passed through directly since the value IS already std::any. *)
Definition apply_pred (input : symbols_semty [1; 2]) : nat :=
  let '(v1, rest) := input in
  let '(v2, _) := rest in
  getSemVal v1 + getSemVal v2.

(* Wrapper that constructs a concrete value and applies the predicate *)
Definition test_pred (a b : nat) : nat :=
  apply_pred (mkSemVal a, (mkSemVal b, tt)).

End AnyCastNestedPair.

Crane Extraction "any_cast_nested_pair" AnyCastNestedPair.
