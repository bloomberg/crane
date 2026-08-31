(** Loopify infers a saved-frame field type with [decltype] over a
    reconstructed call expression, and that expression contains [std::declval]
    in an evaluated position:

    {v
      static assertion failed ... std::declval can only be used in an
      unevaluated context
    v} *)

From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.

Module LoopifyFrameDeclval.

Definition g (l : list nat) : list (nat * nat) := list_prod l l.

End LoopifyFrameDeclval.

Crane Extraction "loopify_frame_declval" LoopifyFrameDeclval.
