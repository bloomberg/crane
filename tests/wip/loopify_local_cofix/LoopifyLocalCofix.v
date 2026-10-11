(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: under [Set Crane Loopify], a local [cofix] with a parameter is
    loopified as if its corecursive call consumed stack.  The transform
    rewrites [go] into a [CraneEnter] loop and drops its [_self_go]
    parameter, but the corecursive call sits inside the lazy thunk that
    builds the stream's tail, which still calls [_self_go(_self_go, n + 1)]:
    "use of undeclared identifier '_self_go'".  A call under a lazy thunk
    returns at once and needs no loop; without Loopify this compiles. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LoopifyLocalCofix.

CoInductive stream := Cons : nat -> stream -> stream.

Fixpoint take (n : nat) (s : stream) : list nat :=
  match n with 0 => [] | S m => match s with Cons x t => x :: take m t end end.

Definition from_list (l : list nat) : stream :=
  (cofix go (n : nat) : stream := Cons (List.length l + n) (go (S n))) 0.

Definition result : nat := fold_left Nat.add (take 3 (from_list [7; 7])) 0.

End LoopifyLocalCofix.

Set Crane Loopify.
Crane Extraction "loopify_local_cofix" LoopifyLocalCofix.
