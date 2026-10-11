(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: where a loopified function's continuation frame saves a child
    it will recurse into as an owning copy, the handler that resumes the
    frame moves the copy into a local and pushes a pointer into that local,
    which dies when the handler returns, before the pushed frame is read.
    AddressSanitizer, which this test is compiled with, reports
    stack-use-after-scope.  A child the frame can save as a pointer into the
    tree being walked is fine (see [regression/loopify_cont_box_pointer]);
    the frame falls back to an owning copy, and the push does not follow,
    - in [sz], where the child [b] comes out of a [std::pair] field (the
      [Mapping.Std] representation of [prod]): [sz] is a method -- the
      closure in [read_with] makes it one -- the frame saves [t b], and the
      push is [CraneEnter{&b}];
    - in [subs], where a closure captures the sibling [l]: the frame saves
      both children as [crane::shared_box]es, and the push is
      [CraneEnter{crane_raw(a2)}] of the local copy, whose value a shared box
      holds inline. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.Std.

Module LoopifyOwnedChildPointer.

Inductive t := N : nat -> (t * t) -> t | E : t.

Fixpoint sz (x : t) : nat := match x with E => 0 | N n (a, b) => n + sz a + sz b end.

Definition leaf (n : nat) : t := N n (E, E).

Inductive reader := Reader : (nat -> nat) -> reader.
Definition read_with (x : t) : reader := Reader (fun k => k + sz x).
Definition read (r : reader) (k : nat) : nat := match r with Reader f => f k end.

Definition size : nat := read (read_with (N 2 (leaf 3, leaf 4))) 0.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

Fixpoint sum (t : tree) : nat := match t with Leaf => 0 | Node l x r => sum l + x + sum r end.

Fixpoint subs (t : tree) : list (nat -> nat) :=
  match t with Leaf => [] | Node l x r => (fun y => y + sum l) :: subs l ++ subs r end.

Definition t0 : tree := Node (Node Leaf 1 Leaf) 2 (Node (Node Leaf 3 Leaf) 4 Leaf).

Definition left_sums : nat := fold_left (fun a f => a + f 0) (subs t0) 0.

End LoopifyOwnedChildPointer.

Set Crane SharedVariant.
Set Crane Loopify.
Crane Extraction "loopify_owned_child_pointer" LoopifyOwnedChildPointer.
