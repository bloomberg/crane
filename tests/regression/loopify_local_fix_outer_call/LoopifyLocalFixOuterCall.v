From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Loopify.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Under Loopify, a structurally recursive function whose recursive call sits
    inside a local [let fix] accumulator: the explicit-stack frame for the
    local fix is built from [a1], a name only declared as a frame member, so
    the generated code does not compile.  Under CRANE_CHECK_IR=1 (the test
    suite) extraction stops first: "moved value read: in ...g, a1 is read
    after it is moved". *)
Module LoopifyLocalFixOuterCall.

Fixpoint g (l : list nat) : list nat :=
  match l with
  | [] => l
  | h :: r =>
    let fix go (m : list nat) (acc : list nat) {struct m} : list nat :=
      match m with [] => acc | e :: rest => go rest (e :: g r) end in
    go l []
  end.

End LoopifyLocalFixOuterCall.

Crane Extraction "loopify_local_fix_outer_call" LoopifyLocalFixOuterCall.
