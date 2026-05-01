From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module LoopifyMutualCountdown.

(** Loopification handles many self-recursive functions, but this probes a
    mutually recursive countdown.  The Rocq computation is total and uses only
    bounded numeric values in the C++ test.  With [Set Crane Loopify.], Crane
    still emits [even_countdown] and [odd_countdown] as ordinary mutually
    recursive C++ calls instead of a loop, so a deep countdown overflows the C++
    stack. *)

Set Crane Loopify.

Fixpoint even_countdown (n : nat) : bool :=
  match n with
  | O => true
  | S n' => odd_countdown n'
  end
with odd_countdown (n : nat) : bool :=
  match n with
  | O => false
  | S n' => even_countdown n'
  end.

End LoopifyMutualCountdown.

Crane Extraction "loopify_mutual_countdown" LoopifyMutualCountdown.
