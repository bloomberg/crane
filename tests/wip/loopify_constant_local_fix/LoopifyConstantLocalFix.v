(** Found by Ephyra round 23. Under [Set Crane Loopify], a local fixpoint
    inside a top-level constant is not loopified: the constant's static
    initialiser keeps the recursive [go_impl] lambda, while the same local
    fixpoint inside a function ([from_n]) gets an explicit stack.
    Expected: [million = 1000000] and [from_n 1000000 = 1000000].
    Actual: [million] overflows the stack during static initialisation
    (segfault before [main]). *)
From Crane Require Import Mapping.NatIntStd.
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
