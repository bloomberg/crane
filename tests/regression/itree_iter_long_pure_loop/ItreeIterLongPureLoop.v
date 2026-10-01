(* A reified [ITree.iter] whose step answers at once, a million times.

   [itree_iter] built the [Tau]-guarded tree eagerly: a step that returned a
   [Ret] went straight into the continuation, which built the next iteration,
   one C++ frame per step -- so a long pure loop overflowed the stack while
   the tree was being built, before anything ran it.  [itree_bind] recursed
   down [Tau] chains the same way.

   Expected: [count_down 1000000] runs to 0.
   Before:   a stack overflow. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITreeReified.
From ITree Require Import ITree.

Module ItreeIterLongPureLoop.
  Definition step (n : nat) : itree void1 (nat + nat) :=
    match n with
    | O => Ret (inr O)
    | S k => Ret (inl k)
    end.

  Definition count_down (n : nat) : itree void1 nat := ITree.iter step n.

  Definition after_taus (n : nat) : itree void1 nat :=
    ITree.bind (count_down n) (fun r => Ret (S r)).
End ItreeIterLongPureLoop.

Crane Extraction "itree_iter_long_pure_loop" ItreeIterLongPureLoop.
