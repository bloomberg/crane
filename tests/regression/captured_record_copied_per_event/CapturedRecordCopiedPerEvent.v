(** Crane bug (performance): a continuation that captures a large record is
    copied into a fresh thunk at every node of the tree it binds over, and
    every copy copied the record.  A loop whose body binds such a
    continuation over a computation of [k] events therefore did work
    proportional to [k] times the record's size per step.

    Reduced from Vellvm, [Semantics/Denotation.v] [denote_block]: its
    continuations capture the CFG block, and [denote_code] triggers one event
    per instruction; the profile of the loop-phi-arith benchmark spent a
    quarter of its time copying and destroying blocks.

    The t.cpp times [run n k] and asserts a bound a copying implementation
    misses by a wide margin. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.
From ITree Require Import ITree.
Import ITreeNotations.
Local Open Scope itree_scope.

Module CapturedRecordCopiedPerEvent.
  Record leaf : Type := mkLeaf { l1 : list nat ; l2 : list nat ; l3 : list nat ; l4 : list nat }.
  Record mid : Type := mkMid { m1 : leaf ; m2 : leaf ; m3 : leaf ; m4 : leaf }.
  Record blk : Type := mkBlk { b1 : mid ; b2 : mid ; b3 : mid ; b4 : mid ; tag : nat }.

  Definition lf (n : nat) : leaf := mkLeaf [n] [n] [n] [n].
  Definition md (n : nat) : mid := mkMid (lf n) (lf n) (lf n) (lf n).
  Definition mk (n : nat) : blk := mkBlk (md n) (md n) (md n) (md n) n.

  Variant tickE : Type -> Type := Tick : tickE unit.

  (* [k] events, as [denote_code] triggers one per instruction. *)
  Fixpoint ticks (k : nat) : itree tickE unit :=
    match k with O => Ret tt | S k' => trigger Tick ;; ticks k' end.

  (* [denote_block]: the continuation captures the block. *)
  Definition step (b : blk) (k : nat) : itree tickE nat :=
    ticks k ;; Ret (tag b).

  Fixpoint steps (n k : nat) (b : blk) (acc : nat) : itree tickE nat :=
    match n with
    | O => Ret acc
    | S n' => x <- step b k ;; steps n' k b (acc + x)
    end.

  (* Answer every event. *)
  Fixpoint run (fuel : nat) (t : itree tickE nat) : option nat :=
    match fuel with
    | O => None
    | S f => match observe t with
             | RetF r => Some r
             | TauF t' => run f t'
             | VisF e k => match e in tickE T return (T -> itree tickE nat) -> option nat with
                           | Tick => fun k => run f (k tt)
                           end k
             end
    end.
End CapturedRecordCopiedPerEvent.

Crane Extraction "captured_record_copied_per_event" CapturedRecordCopiedPerEvent.
