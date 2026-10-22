From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.

Set Crane Loopify.

(** A local a block template declares, kept across a recursive call.

    [twice n] is a block template: Crane declares the variable it binds and
    the template assigns it ([%result = ...]).  Under Loopify the
    continuation frame keeps [d] across the call of [doubles m], but the
    frame read the types of the locals in scope off their declarations and
    did not count the template's, so [d] had no type: its field was spelt
    [decltype(d)] before any [d] exists, and the continuation assigned an
    undeclared [d]. *)

Axiom twice : forall {E} `{consoleE -< E}, nat -> itree E nat.
Crane Extract Inlined Constant twice => "%result = %a0 * 2".

Module LoopifyBlockTemplateFrame.

Fixpoint doubles (n : nat) : itree ioE (list nat) :=
  match n with
  | O => Ret nil
  | S m =>
    d <- twice n ;;
    rest <- doubles m ;;
    Ret (cons d rest)
  end.

End LoopifyBlockTemplateFrame.

Crane Extraction "loopify_block_template_frame" LoopifyBlockTemplateFrame.
