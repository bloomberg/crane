From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Memory safety: use after return.  A corecursive branch builds a local
    fixpoint lambda [go] that captures [m] (a local of [h]) by reference, then
    returns [stream::lazy_([=] { return go(...); })].  The thunk copies [go]
    but not what it refers to; when it is forced after [h] returned, [m] is a
    dead stack slot, so [h(m)] recurses on garbage (the test runs away in time
    and memory).  CRANE_CHECK_IR=1 reports it first: "closure captures: the
    local fixpoint lambda go reads its scope by reference and escapes it". *)
Module CofixThunkDanglingCapture.

CoInductive stream : Type := SCons : nat -> stream -> stream.
CoFixpoint sconst (n : nat) : stream := SCons n (sconst n).

Fixpoint h (n : nat) : stream :=
  match n with
  | O => sconst 0
  | S m => let fix go (l : list nat) (acc : stream) {struct l} : stream :=
             match l with [] => h m | _ :: r => go r acc end in
           go [1; 2] (match n with O => h m | S _ => sconst 2 end)
  end.

Fixpoint stake (k : nat) (s : stream) : list nat :=
  match k with O => [] | S k' => match s with SCons x r => x :: stake k' r end end.

Definition t : nat := fold_left Nat.add (stake 3 (h 3)) 0.

End CofixThunkDanglingCapture.

Crane Extraction "cofix_thunk_dangling_capture" CofixThunkDanglingCapture.
