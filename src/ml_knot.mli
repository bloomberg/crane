(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The knot of a well-founded recursion tied directly.

    Well-founded recursion defined with [Equations] (or the [Fix]/[Wf]
    combinators) extracts as two definitions: a functional [g x rec] that
    recurses by calling its parameter [rec], and the function [f x = g x
    (fun y => f y)] tying the knot.  Its recursion is hidden in a closure it
    passes, which no loop can be made of.

    Where Loopify loopifies [f] ({!Table.should_loopify}), its body becomes
    the functional's, each call of [rec] a call of [f] itself: ordinary
    recursion, planned and lowered as any other.  Only that knot is tied:
    [f]'s body is a call of a functional defined without recursion, at the
    type arguments the call writes, passing it one eta-expansion of [f] --
    over [f]'s arguments and any erased ones, a proof that the recursion is
    well-founded -- and nothing else naming [f]; the functional's parameter
    is called with an argument for each of the expansion's binders and
    never read otherwise; and [f] is not polymorphic.  The functional is
    left in place. *)

val structure : Miniml.ml_structure -> Miniml.ml_structure
