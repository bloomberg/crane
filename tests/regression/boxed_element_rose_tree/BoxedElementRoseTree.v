From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A rose tree whose children are a mapped container with a [Boxed
    Element] wrapper, as ParseALot maps lists: the element is boxed exactly
    where it recurses through the container, so [list rose] is
    [crane::list<crane::box<rose>>] while [list nat] stays unboxed. *)
Module BoxedElementRoseTree.

Inductive rose := Node (n : nat) (kids : list rose).

Fixpoint size (r : rose) : nat :=
  match r with
  | Node _ ks =>
    S ((fix go (l : list rose) : nat :=
          match l with
          | [] => 0
          | k :: t => size k + go t
          end) ks)
  end.

Fixpoint total (r : rose) : nat :=
  match r with
  | Node n ks =>
    n + (fix go (l : list rose) : nat :=
           match l with
           | [] => 0
           | k :: t => total k + go t
           end) ks
  end.

Definition labels (r : rose) : list nat :=
  match r with
  | Node n ks => n :: map (fun k => match k with Node m _ => m end) ks
  end.

Definition sample : rose :=
  Node 1 [Node 2 []; Node 3 [Node 4 []; Node 5 []]; Node 6 []].

Definition sample_size : nat := size sample.
Definition sample_total : nat := total sample.
Definition sample_labels : list nat := labels sample.

End BoxedElementRoseTree.

Crane Extract Inductive list =>
  "crane::list<%elem>"
  [ "crane::list<%elem>{}"
    "crane::cons(%a0, %a1)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.tail(); %br1 }"
  Boxed Element "crane::box<%t0>"
  From "conslist.h".

Crane Extraction "boxed_element_rose_tree" BoxedElementRoseTree.
