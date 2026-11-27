(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An interaction-tree-shaped coinductive under SharedVariant: [tree] is a
    record around one [treeF] layer, a shared variant, so the layer is one
    word naming its own block.  A [crane::lazy] holds such a layer, once
    evaluated, in its own word rather than in a node ([Ret] and [Vis] build
    no node), while a suspended layer ([Tau] under a cofix) keeps its thunk
    node.  The driver checks the semantics of both kinds of cell: forcing
    once through aliases, a thunk that throws and is forced again, a thunk
    that forces itself, long delegated chains, copies and moves, a nullary
    alternative, and boxing into [crane::obj]. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatInt.

Module LazyDirectLayer.

Variant treeF (tree : Type) : Type :=
| RetF (r : nat)
| TauF (t : tree)
| VisF (e : nat) (k : nat -> tree)
| StopF.

Arguments RetF {tree} r.
Arguments TauF {tree} t.
Arguments VisF {tree} e k.
Arguments StopF {tree}.

CoInductive tree : Type := go { observe : treeF tree }.

Definition Ret (n : nat) : tree := go (RetF n).
Definition Tau (t : tree) : tree := go (TauF t).
Definition Vis (e : nat) (k : nat -> tree) : tree := go (VisF e k).
Definition Stop : tree := go StopF.

(** [n] taus before a [Ret]: each tau is suspended. *)
CoFixpoint taus (n : nat) (r : nat) : tree :=
  match n with
  | O => Ret r
  | S m => Tau (taus m r)
  end.

(** Asks [n] events, adding up the answers. *)
CoFixpoint ask (n : nat) (acc : nat) : tree :=
  match n with
  | O => Ret acc
  | S m => Vis m (fun a => ask m (acc + a))
  end.

(** The tree [t] runs to, answering every event with [e + 1], within [fuel]
    steps. *)
Fixpoint run (fuel : nat) (t : tree) : option nat :=
  match fuel with
  | O => None
  | S f =>
      match observe t with
      | RetF r => Some r
      | TauF u => run f u
      | VisF e k => run f (k (S e))
      | StopF => None
      end
  end.

End LazyDirectLayer.

Set Crane SharedVariant.
Set Crane FastVariant.
Crane Extraction "lazy_direct_layer" LazyDirectLayer.
