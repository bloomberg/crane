(** Well-founded recursion through an [Equations] clause helper.

    A [with] clause makes [Equations] generate a helper, [zeros_clause_2],
    that the functional passes the recursion to as an argument.  The knot
    [Ml_knot] ties is then read in the helper's body, which it instantiates
    where the functional calls it: [zeros] recurses by calling itself, and
    is loopified as [plain] is, over a list deeper than the C++ stack. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Equations Require Import Equations.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Set Crane Loopify.

Module LoopifyEquationsWithClause.

Equations zeros (l : list nat) : nat by wf (length l) lt :=
  zeros [] := 0;
  zeros (x :: xs) with Nat.eqb x 0 := {
    | true := S (zeros xs);
    | false := zeros xs }.

Equations plain (l : list nat) : nat by wf (length l) lt :=
  plain [] := 0;
  plain (x :: xs) := x + plain xs.

End LoopifyEquationsWithClause.

Crane Extraction "loopify_equations_with_clause" LoopifyEquationsWithClause.
