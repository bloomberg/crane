From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Loopify.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Under Loopify, [g r (g r a)] in two places of the same branch (one under a
    pair match, one inside a [filter] predicate): the second continuation frame
    is built as [_after_g_in_pair_2{a, a1}] with the [const List &] where its
    field is a [std::shared_ptr]: "no viable conversion from 'const List<...>'
    to 'std::shared_ptr<List<...>>'". *)
Module LoopifyNestedCallFrameField.

Fixpoint g (l : list (nat * bool)) (a : list nat) : list nat :=
  match l with
  | [] => []
  | h :: r => filter (fun y : nat => Nat.eqb (length (g r (g r a))) y)
                     (match h with (p, q) => g r (g r a) end)
  end.

End LoopifyNestedCallFrameField.

Crane Extraction "loopify_nested_call_frame_field" LoopifyNestedCallFrameField.
