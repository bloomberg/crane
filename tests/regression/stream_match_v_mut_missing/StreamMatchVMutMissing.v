From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A local fixpoint over a list of streams, called on a literal [[]], matches
    an element with [SCons h _]: the inlined match takes the element by
    mutable reference, [a0.v_mut()], which a coinductive type does not have
    ("no member named 'v_mut' in 'stream'"). *)
Module StreamMatchVMutMissing.

CoInductive stream : Type := SCons : nat -> stream -> stream.

Definition g (n : nat) : nat * nat :=
  let fix go (l : list stream) (acc : nat * nat) {struct l} : nat * nat :=
    match l with [] => (0, 0) | e :: _ => match e with SCons h _ => (n, h) end end in
  go [] (0, 0).

End StreamMatchVMutMissing.

Crane Extraction "stream_match_v_mut_missing" StreamMatchVMutMissing.
