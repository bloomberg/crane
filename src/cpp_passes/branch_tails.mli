(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the branches of a conditional end with, written once.

    {!drop_trailing_returns}: a [return;] that ends a function's body is
    where control goes anyway.  Lowering writes one at the end of every
    branch of a [void] function -- [if (c) { ...; return; } else { return; }]
    -- and a [return;] that is the last statement of the body, or of a branch
    of a conditional or a match that is -- or of a custom match whose
    template ends with its one branch, a pair taken apart -- is dropped.  A branch that would be
    left empty keeps its [return;] -- an early exit reads better than an
    empty branch -- except an [else] branch, which is then not written.

    {!hoist_common_suffixes}: when both branches of an [if] end with the same
    statements, those statements run after the [if] whichever branch is
    taken, and are written there once -- Loopify's [i = (i + 1);] at the end
    of each branch of a loop's body.  Only plain statements move (an
    assignment or an expression), so no [return], [break], [continue] or
    [throw] changes where it jumps from, and only those reading no variable
    either branch declares, so none leaves its variable's scope.  A [then]
    branch left empty takes the [else] branch's place under the negated
    condition, where that is written plainly ([==] for [!=], a variable's
    negation); otherwise nothing is hoisted.

    Passes of {!Pipeline}, run through {!Erasure} after the mappings are
    instantiated: a match on a [bool] is a custom match until then, and
    only its instantiation makes it the [if] these passes read. *)

val drop_trailing_returns : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
val hoist_common_suffixes : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
