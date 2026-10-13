(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a definition emitted as a function of no parameters -- a
    cofixpoint, or a definition whose body only throws -- is named without
    being called when it is reached through a module alias.  Whether naming
    a global calls it is read from the cofixpoint and throwing-value tables,
    which are keyed by the name a definition was registered under; [B.ones]
    for [Module B := A] is not found there, so it is passed as the function
    [stream ()] where a [stream] is wanted, and [B.absurd_nat h] is the
    function pointer in a conditional with a [uint64_t].  [Include] is
    fine: it makes copies with declarations of their own. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module AliasThunkReference.

Module A.
  CoInductive stream := Cons : nat -> stream -> stream.
  CoFixpoint ones : stream := Cons 1 ones.
  Definition hd (s : stream) : nat := match s with Cons x _ => x end.
  Definition absurd_nat (H : 0 = 1) : nat := False_rect _ (O_S 0 H).
End A.

Module B := A.

Definition from_cofix : nat := B.hd B.ones.

Definition from_throwing : nat :=
  match Nat.eq_dec 0 1 with left h => B.absurd_nat h | right _ => 9 end.

End AliasThunkReference.

Crane Extraction "alias_thunk_reference" AliasThunkReference.
