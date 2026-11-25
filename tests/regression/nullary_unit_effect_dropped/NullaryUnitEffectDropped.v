(* A nullary inlined constant in the tail of a [unit]-returning function was
   dropped: [f] extracted to [void f() { return; }], losing the throw.  Fixed:
   [Cpp_build.return_into_void] treated an inline custom's text (and foreign
   template text) as a pure value and dropped it; only the text says what it
   does, so it is now kept as an expression statement before the [return;]. *)
From Crane Require Import Extraction.
From Crane Require Import Monads.ITree.

Variant giveupE : Type -> Type := GiveUp : giveupE unit.

Definition give_up : itree giveupE unit := embed GiveUp.

Crane Extract Inlined Constant give_up => "throw 0".

Module NullaryUnitEffectDropped.
  Definition f (u : unit) : itree giveupE unit := give_up.
End NullaryUnitEffectDropped.

Crane Extraction "nullary_unit_effect_dropped" NullaryUnitEffectDropped.
