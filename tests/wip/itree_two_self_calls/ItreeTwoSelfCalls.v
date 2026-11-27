(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: an erased-mode [itree] fixpoint that makes two self-calls in
    sequence ([walk f l m;; walk f m r], the shape of an in-place quicksort)
    fails the IR check under Loopify:

      Crane IR check (control lowering): a loop the plan commits to was left
      as generated (left as generated): ...walk

    At result type [nat] (the first call's result discarded) the same shape
    fails the typed-fit check instead: a [nat] is put in a slot of type
    [itree tickE nat].  This is why [st_quicksort] used to go through
    [rec]/[call] and a hand-written stack. *)

From ITree Require Import ITree.
From Crane Require Import Mapping.NatInt Monads.ITree.
Import Monads.
Local Open Scope monad_scope.

Variant tickE : Type -> Type := Tick (n : nat) : tickE unit.

Module ItreeTwoSelfCalls.
  (** Visits the midpoints of [l..r], left half first; [fuel] bounds the
      depth. *)
  Fixpoint walk (fuel : nat) (l r : nat) : itree tickE unit :=
    match fuel with
    | O => Ret tt
    | S f =>
      if Nat.ltb l r then
        let p := Nat.div (l + r) 2 in
        walk f l (p - 1);;
        walk f (p + 1) r
      else Ret tt
    end.

  Definition run (n : nat) : itree tickE unit := walk n 0 n.
End ItreeTwoSelfCalls.

Set Crane Loopify.
Crane Extraction "itree_two_self_calls" ItreeTwoSelfCalls.
