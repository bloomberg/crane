(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A loopified function with two recursive calls in sequence after an alias
    of a polymorphic function, which translation puts in place of its uses
    rather than binding.  The recursion plan named the binders after it by
    their level in the body as written, one deeper than the level
    translation declares them at, so the second call's result was taken for
    the first's: its frame kept the first call's live variables, among them
    [m], dead after the second call, and the frame check failed. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Set Crane Loopify.

Module InlinedAliasResumeFrame.

Fixpoint h (n : nat) : nat :=
  match n with
  | O => 1
  | S m =>
    let e := fun (A : Type) => @nil A in
    let r1 := h m in
    let r2 := h m in
    r1 + r2 + n + length (e nat) + length (e bool)
  end.

Definition h3 : nat := h 3.

End InlinedAliasResumeFrame.

Crane Extraction "inlined_alias_resume_frame" InlinedAliasResumeFrame.
