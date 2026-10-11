(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a method recursing twice over a shared-variant tree -- [sum],
    methodified and loopified -- saves the right child in its continuation
    frame as an owning [crane::shared_box], moves it into a local when the
    frame is resumed, and pushes [CraneEnter{crane_raw(a2)}]: a pointer to
    the value held inside that local, which goes out of scope at the end of
    the handler, before the pushed frame is read.  The result is right only
    as long as nothing reuses the stack slot; AddressSanitizer, which this
    test is compiled with, reports stack-use-after-scope. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LoopifyContBoxPointer.

Inductive tree := Leaf | Node : tree -> nat -> tree -> tree.

Fixpoint insert (k : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf k Leaf
  | Node l k' r =>
      if Nat.ltb k k' then Node (insert k l) k' r
      else if Nat.ltb k' k then Node l k' (insert k r)
      else t
  end.

Fixpoint sum (t : tree) : nat :=
  match t with Leaf => 0 | Node l k r => sum l + k + sum r end.

Definition build (n : nat) : tree := fold_left (fun t k => insert k t) (seq 0 n) Leaf.

(** Read through a closure, which is what makes [sum] a method. *)
Inductive reader := Reader : (nat -> nat) -> reader.
Definition read_with (t : tree) : reader := Reader (fun x => x + sum t).
Definition read (r : reader) (x : nat) : nat := match r with Reader f => f x end.

Definition total : nat := read (read_with (build 20)) 0.

End LoopifyContBoxPointer.

Set Crane SharedVariant.
Crane Loopify map.
Crane Extraction "loopify_cont_box_pointer" LoopifyContBoxPointer.
