(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* WIP: TODO from src/mlutil.ml line 1304:
   "handle some more cases" in iota_red

   The `iota_red` function performs generalized iota-reduction: it simplifies
   `MLcase(_, MLcons(typ, r, a), br)` when the scrutinee is a known constructor.
   The current implementation handles:
   - Pusual r': standard constructor match
   - Prel 1 when exactly 1 bound variable: singleton rel pattern
   - Pwild when 0 bound variables: pure wildcard
   Missing cases include:
   - Prel 1 when there are multiple bound variables
   - Pwild when bound variables exist
   - Other complex patterns

   When the missing cases are hit, `raise Impossible` is caught by `iota_gen`
   and the optimization is simply skipped (code is correct but unoptimized).
   This means the test PASSES but produces suboptimal extraction.

   Bug status: DOCUMENTED (passes, but iota reduction is skipped for complex
   patterns, potentially generating less efficient C++ code). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module TodoIotaComplexPattern.

  Inductive Triple (A B C : Type) :=
    | MkTriple : A -> B -> C -> Triple A B C.
  Arguments MkTriple {A B C}.

  (* A function that nests pattern matches in a way that might trigger
     the unhandled iota-reduction case. The inner match on a known constructor
     followed by another match could require iota reduction. *)
  Definition sum_triple (t : Triple nat nat nat) : nat :=
    match t with
    | MkTriple a b c => a + b + c
    end.

  (* Nested patterns that might exercise iota_gen *)
  Definition rotate_triple {A B C : Type} (t : Triple A B C) : Triple B C A :=
    match t with
    | MkTriple a b c => MkTriple b c a
    end.

  Definition test1 : nat := sum_triple (MkTriple 1 2 3).
  Definition test2 : Triple bool nat nat := rotate_triple (MkTriple 10 true 20).

End TodoIotaComplexPattern.

Crane Extraction "todo_iota_complex_pattern" TodoIotaComplexPattern.
