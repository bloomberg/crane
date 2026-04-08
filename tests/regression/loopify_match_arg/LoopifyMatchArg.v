(* Copyright 2026 Joomy Korkut.
   Distributed under the terms of the GNU LGPL v2.1 license.

   Minimal repro for two Crane Loopify bugs:

   Bug 1 – Missing #include <vector>.
     When loopify transforms a recursive function into an iterative one
     using an explicit stack, the generated C++ uses std::vector<_Frame>
     but the header does not emit #include <vector>.

   Bug 2 – Partial loopification with match on constructor argument.
     When a Fixpoint matches on its recursive argument and one branch
     also matches on a *constructor field* (e.g. a cell/tag carried
     inside a Cons), the Nil branch is loopified (assigns _result,
     returns void) but the Cons branch is left as a recursive call
     (returns the result type).  The two lambdas in the Overloaded
     visitor then have mismatched return types, which makes std::visit
     ill-formed. *)

Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyMatchArg.

  Inductive cell : Type := Wall | Empty | Dot.

  (** Count the number of [Dot] cells in a list.
      The match on [c] inside the [Cons] branch triggers bug 2. *)
  Fixpoint count_dots (xs : list cell) : nat :=
    match xs with
    | nil => 0
    | cons c rest =>
      match c with
      | Dot => 1 + count_dots rest
      | _   => count_dots rest
      end
    end.

  (** A plain recursive length — triggers bug 1 (missing <vector>)
      when loopify converts it to an explicit-stack loop. *)
  Fixpoint my_length (xs : list cell) : nat :=
    match xs with
    | nil => 0
    | cons _ rest => 1 + my_length rest
    end.

End LoopifyMatchArg.

Set Crane Loopify.
Crane Extraction "loopify_match_arg" LoopifyMatchArg.
