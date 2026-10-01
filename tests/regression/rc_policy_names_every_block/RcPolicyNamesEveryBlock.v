(* [Crane NonAtomicRc] selects non-atomic reference counts, and the two
   policies give one runtime type two layouts.  [crane::fn] kept them apart
   with an inline namespace named after the policy, so a program mixing units
   built under both failed to link; but [crane::obj] and [crane::lazy] hold the
   same count and sat outside that namespace, so the linker silently kept one
   layout for both -- a threaded unit could run on non-atomic counts.

   Expected: every block that holds a count -- a closure, an erased value's
   box, a coinductive's cell -- is declared in the policy's namespace.
   Before:   [crane::rc_local::obj] and [crane::rc_local::lazy] did not exist. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Set Crane NonAtomicRc.

Module RcPolicyNamesEveryBlock.
  CoInductive stream : Type := SCons : nat -> stream -> stream.

  CoFixpoint from (n : nat) : stream := SCons n (from (S n)).

  Definition hd (s : stream) : nat := match s with SCons x _ => x end.

  Definition twice (f : nat -> nat) (x : nat) : nat := f (f x).

  Definition boxed : {T : Set & T} := existT (fun T : Set => T) nat 3.
End RcPolicyNamesEveryBlock.

Crane Extraction "rc_policy_names_every_block" RcPolicyNamesEveryBlock.
