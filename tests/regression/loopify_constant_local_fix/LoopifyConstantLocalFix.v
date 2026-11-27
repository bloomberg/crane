(** Found by Ephyra (round 23). Under [Set Crane Loopify], a non-tail
    local fixpoint inside a top-level constant and the same one inside a
    function ([from_n]).

    Expected: [million = 1000000] and [from_n 1000000 = 1000000].

    Fixed: [million] overflowed the stack during static initialisation
    (segfault before [main]).  Translation lowered a local fixpoint's
    frame machine only in a function's body, as the C++-level Loopify
    once did, so the constant's initialiser kept the recursive [go_impl]
    lambda.  A constant's initialiser now lowers its local machines as a
    function's body does. *)
From Crane Require Import Mapping.NatInt.
From Crane Require Import Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Loopify.

Module LoopifyConstantLocalFix.

Definition from_n (n : nat) : nat :=
  length (let fix go (l : list nat) {struct l} : list nat :=
    match l with [] => [] | x :: rest => x :: go rest end
  in go (repeat 1 n)).

Definition million : nat :=
  length (let fix go (l : list nat) {struct l} : list nat :=
    match l with [] => [] | x :: rest => x :: go rest end
  in go (repeat 1 (Nat.pow 10 6))).

End LoopifyConstantLocalFix.

Crane Extraction "loopify_constant_local_fix" LoopifyConstantLocalFix.
