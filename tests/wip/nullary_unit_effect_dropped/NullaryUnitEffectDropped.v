(* A nullary inlined constant in the tail of a [unit]-returning function is
   dropped: [f] extracts to [void f(Unit) { return; }], losing the throw.
   Give [give_up] an argument and the call is kept.  Likely [cofix_wrap] in
   src/gen_functions.ml, which treats a void tail that is a [CPPglob] with
   an inline custom as a pure value. *)
From Crane Require Import Extraction.
From Crane Require Import Monads.ITree.

Variant giveupE : Type -> Type := GiveUp : giveupE unit.

Definition give_up : itree giveupE unit := embed GiveUp.

Crane Extract Inlined Constant give_up => "throw 0".

Module NullaryUnitEffectDropped.
  Definition f (u : unit) : itree giveupE unit := give_up.
End NullaryUnitEffectDropped.

Crane Extraction "nullary_unit_effect_dropped" NullaryUnitEffectDropped.
