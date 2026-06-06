(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Regression test for missing any_cast in sigT with nested erased pairs.

   When extracting a sigT with a dependent payload_ty that is a computed
   type family, the C++ payload field has type std::any (because payload_ty
   renders as std::any when the type family can't be resolved statically).

   Two bugs manifest:

   1. In the branch where payload_ty n = A (a type variable), the generated
      code does "return a1;" where a1 : std::any but the function return
      type is T1 (a template parameter).  Missing: any_cast<T1>(a1).

   2. In the branch where payload_ty n = nested pair, the inner pair match
      goes through apply_fixc_to_nested (translation.ml ~line 7531).
      The catch-all generates any_cast<T1>(a0) for Tvar-typed variables.
      For template functions this is correct, but the related ConstRef
      variant (from module functors) would generate any_cast<std::any>(v)
      which throws bad_any_cast — the same class of bug fixed in the outer
      path at line 7450.

   This test FAILS at compile time due to bug #1: the S branch tries to
   return std::any as T1 without an any_cast. *)

From Crane Require Import Mapping.NatIntStd.
Require Crane.Extraction.

Module AnyCastNested.

Section WithA.
Variable A : Type.

(* Dependent type family making sigT truly dependent → Obj.magic in
   extraction, which triggers scrut_is_magic for the pair match. *)
Fixpoint payload_ty (n : nat) : Type :=
  match n with
  | O => (nat * (nat * A))%type
  | S _ => A
  end.

(* Extract the innermost value from the nested pair payload.
   - O branch: nested pair destructuring via fix_a_fired path
   - S branch: direct return of the erased payload *)
Definition extract_a (s : { n : nat & payload_ty n }) : A :=
  match s return A with
  | existT _ O payload =>
    let '(_, rest) := payload in
    let '(_, v) := rest in
    v
  | existT _ (S _) a => a
  end.

End WithA.

(* Concrete test: A = nat.  extract_a<uint64_t>(existT _ 1 x) hits the S
   branch where payload_ty(S _) = A = nat, so the payload is erased to
   std::any containing a uint64_t.  The fix inserts any_cast<uint64_t>(a1)
   so the return is well-typed. *)
Definition test_extract (x : nat) : nat :=
  extract_a nat (existT _ 1 x).

End AnyCastNested.

Crane Extraction "any_cast_nested" AnyCastNested.
