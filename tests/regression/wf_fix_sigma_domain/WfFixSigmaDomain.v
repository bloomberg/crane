(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: an Equations definition by well-founded recursion on a measure
    of two arguments does not compile.  Equations packs the arguments into a
    [sigma] and recurses with [Fix_F]; Crane lifts that into a helper
    [template <typename T1> static uint64_t sw_crane_Fix_F(const T1 x)] in
    which [T1] is the packed argument's type, but the call site instantiates
    [T1] with the result type: [sw_crane_Fix_F<uint64_t>(sigma<...>{a, b})].
    The graph's correctness lemma, extracted alongside, gets the same helper
    shape and returns [uint64_t] where it builds a [sw_graph].  One argument
    ([by wf n lt]) is fine. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import Lia.
From Equations Require Import Equations.

Module WfFixSigmaDomain.

Equations sw (a b : nat) : nat by wf (a + b) lt :=
sw 0 b := b;
sw (S a) b := S (sw b a).
Next Obligation. lia. Qed.

Definition result : nat := sw 3 4.

End WfFixSigmaDomain.

Crane Extraction "wf_fix_sigma_domain" WfFixSigmaDomain.
