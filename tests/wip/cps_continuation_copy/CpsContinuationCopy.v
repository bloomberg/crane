From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

(** [sumk] is tail recursive and is loopified into a [for], so it should run in
    constant stack.  It did not: the continuation parameter [k] was a
    [std::function] taken by value and then *copied* into the next
    continuation's capture, rather than moved out of the dying parameter.  Each
    iteration therefore copied the whole chain, and copying a chain of a
    hundred thousand nested [std::function]s recursed a hundred thousand deep
    and overflowed the stack.

    Diagnosis (2026-11-24): that defect is gone.  A continuation is a shared,
    immutable [crane::fn], so the copy is a reference-count increment, and
    [sumk] loopifies (the test was missing [Set Crane Loopify], which it
    needs to be about the loop at all; [List.seq] then builds its list in a
    loop too).  Destroying the chain is iterative as well.  What still
    overflows, at the suite's [-O0], is calling the chain: [_loop_k(0)]
    runs a hundred thousand closures, each tail-calling the next
    ([fun s => k (x + s)]).  OCaml eliminates those tail calls; C++ does not
    promise to, and at [-O0] each level costs some 200 bytes of stack
    through [crane::fn]'s invocation thunk, so about 40000 levels exhaust
    the default 8 MB stack.  The same program passes at [-O1] and [-O2],
    and at [-O0] with a 64 MB stack.  Guaranteed tail calls through closure
    values would need a different calling convention for [crane::fn] (a
    trampoline, or [[clang::musttail]], which needs matching signatures
    the thunk does not have): a design question, not this defect.  Kept in
    wip until it is decided. *)

Module CpsContinuationCopy.

  Fixpoint sumk (l : list nat) (k : nat -> nat) : nat :=
    match l with
    | [] => k 0
    | x :: r => sumk r (fun s => k (x + s))
    end.

  Definition run : nat := sumk (List.seq 0 100000) (fun x => x).

End CpsContinuationCopy.

Set Crane Loopify.

Crane Extraction "cps_continuation_copy" CpsContinuationCopy.
