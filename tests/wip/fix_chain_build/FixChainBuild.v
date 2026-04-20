From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module FixChainBuild.

(** Recursive construction of a closure chain. Each level creates a
    local fixpoint that captures the current [n] AND the previous
    level's closure [prev], then stores the fixpoint in a pair with
    its base value (preventing uncurrying).

    BUG: Each [step] fixpoint uses [&] capture, binding [n] (the
    current stack frame's parameter), [prev] (a local variable),
    and [step] itself. When [build_chain] returns, the stack frame
    is destroyed, and the returned closure holds dangling references. *)

Fixpoint build_chain (n : nat) : nat * (nat -> nat) :=
  match n with
  | O => (0, fun x => x)
  | S n' =>
    let '(_, prev) := build_chain n' in
    let fix step (x : nat) : nat :=
      match x with
      | O => n
      | S x' => S (prev (step x'))
      end
    in (n, step)
  end.

(** test1: build_chain(1) = (1, step1).
    step1(0) = 1.
    step1(2) = S(prev(step1(1))) = S(prev(S(prev(step1(0)))))
             = S(prev(S(prev(1)))) = S(prev(S(1))) = S(prev(2)) = S(2) = 3.
    Pair first + step1(2) = 1 + 3 = 4. *)
Definition test1 : nat :=
  let '(base, f) := build_chain 1 in
  base + f 2.

(** test2: build_chain(2).
    step1 captures prev=id, n=1. step2 captures prev=step1, n=2.
    step2(0) = 2. Result: 2 + step2(0) = 2 + 2 = 4. *)
Definition test2 : nat :=
  let '(base, f) := build_chain 2 in
  base + f 0.

(** test3: build_chain(3). More nesting = more dangling frames.
    step3(0) = 3. Result: 3 + 3 = 6. *)
Definition test3 : nat :=
  let '(base, f) := build_chain 3 in
  base + f 0.

End FixChainBuild.

Crane Extraction "fix_chain_build" FixChainBuild.
