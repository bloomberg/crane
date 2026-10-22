From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.

Set Crane Loopify.

(** A local fixpoint whose recursive calls are all made by a fixpoint
    inside it.

    [f] calls itself only from [ack_m], a fixpoint it applies in place.  A
    machine for [f] leaves those calls where they are, in [ack_m]'s
    closure, but drops the self-parameter they recurse through, so the
    loop it emitted named an undeclared [_self_f].  A local machine does not
    adopt an inner fixpoint as a second entry, so [f] is left recursing
    natively. *)

Module LoopifyLocalFixInnerCallback.

Definition ack (p : nat * nat) : nat :=
  let fix f (m n : nat) : nat :=
    (fix ack_m (n : nat) : nat :=
      match m with
      | 0 => S n
      | S pm =>
        match n with
        | 0 => f pm 1
        | S pn => f pm (ack_m pn)
        end
      end) n in
  f (fst p) (snd p).

Definition small : nat := ack (2, 3).

End LoopifyLocalFixInnerCallback.

Crane Extraction "loopify_local_fix_inner_callback" LoopifyLocalFixInnerCallback.
