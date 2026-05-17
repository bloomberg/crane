(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* TAXIOM ANALYSIS: src/mlutil.ml lines 964, 976, 1585

   Three sites generate Taxiom-typed lambdas. Investigation of each:

   (a) many_lams / anonym_tmp_lams (lines 964, 966): called only from
       general_optimize_fix, where the result is immediately beta-reduced by
       normalize before any C++ translation sees it. Safe.

   (b) anonym_or_dummy_lams (line 976): Crane's extraction.ml never calls this
       function — it always uses anonym_or_dummy_lams_typed, which carries actual
       resolved types. The Taxiom branch is dead for the C++ backend.

   (c) eta_expansion_sign (line 1585): called from case_expunge only when a
       match branch has fewer lambdas than the constructor arity. For well-formed
       Rocq patterns, branches are always lambda-abstracted over all constructor
       arguments, so this path is never taken. If it were triggered (e.g. by a
       synthetic ML term), Taxiom → Tglob(VarRef "axiom") in C++, which is NOT
       filtered by is_cpp_dummy_type (only dummy_type/prop/implicit are), causing
       a C++ compile error with an undeclared type `axiom`.

   All three Taxiom paths are unreachable or eliminated before reaching gen_expr
   for valid Rocq input. This test confirms the common patterns extract cleanly.
   If any of these paths were to become reachable, the resulting C++ would fail
   to compile — making the failure visible. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module TodoEtaExpansionTaxiom.

  Inductive Pair (A B : Type) :=
    | MkPair : A -> B -> Pair A B.
  Arguments MkPair {A B}.

  Definition swap_pair {A B : Type} (p : Pair A B) : Pair B A :=
    match p with
    | MkPair a b => MkPair b a
    end.

  Definition fst_pair {A B : Type} (p : Pair A B) : A :=
    match p with
    | MkPair a _ => a
    end.

  Definition test_swap : Pair bool nat := swap_pair (MkPair 3 true).
  Definition test_fst : nat := fst_pair (MkPair 42 true).

End TodoEtaExpansionTaxiom.

Crane Extraction "todo_eta_expansion_taxiom" TodoEtaExpansionTaxiom.
