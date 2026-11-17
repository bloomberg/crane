From Crane Require Import Extraction.
From Crane.Mapping Require Import NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Set Crane Loopify.

(** A recursive call bound at the top of a function's body, the rest of
    the body after it.

    [csum]'s body matches nothing: it adds [key c] to a local fixpoint
    applied to [kids c], which Normalize binds first.  The machine adopts
    the fixpoint, which calls back into [csum], and reroutes the bound call
    to it.  The machine rewrote its body one top-level statement at a time,
    so the binding never resumed into the addition after it, and the
    rerouted call was left naming the entry, which is no function. *)

Module LoopifyTopLevelCallBinding.

Inductive cell : Type := MkCell { key : nat; kids : list cell }.

Fixpoint csum (c : cell) : nat :=
  key c + (fix go (l : list cell) : nat :=
             match l with [] => 0 | x :: r => csum x + go r end) (kids c).

(** A chain [n] cells deep, each holding [k]. *)
Fixpoint chain (n k : nat) : cell :=
  match n with
  | 0 => MkCell k []
  | S m => MkCell k [chain m k]
  end.

Definition wide : cell := MkCell 1 [MkCell 2 []; MkCell 3 [MkCell 4 []]].

End LoopifyTopLevelCallBinding.

Crane Extraction "loopify_top_level_call_binding" LoopifyTopLevelCallBinding.
