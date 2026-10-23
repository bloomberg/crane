From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A rose tree over a container with a [Boxed Element] wrapper and a
    [Drain] clause, as ParseALot's ConsList.v maps lists: the destructor
    takes a deep tree apart through the drain rather than by recursion. *)
Module BoxedElementDrain.

Inductive rose := Node (n : nat) (kids : list rose).

Fixpoint total (r : rose) : nat :=
  match r with
  | Node n ks =>
    n + (fix go (l : list rose) : nat :=
           match l with
           | [] => 0
           | k :: t => total k + go t
           end) ks
  end.

Fixpoint spine (d : nat) : rose :=
  match d with
  | 0 => Node 1 []
  | S d' => Node 1 [spine d']
  end.

Definition sample : rose := Node 2 [Node 3 []; Node 4 [Node 5 []]].

Definition sample_total : nat := total sample.

End BoxedElementDrain.

Crane Extract Inductive list =>
  "crane::list<%t0>"
  [ "crane::list<%t0>{}"
    "crane::cons(%a0, %a1)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.tail(); %br1 }"
  Boxed Element "crane::box<%t0>"
  Drain "%scrut.drain_each([&](auto&& _e) { %yield(std::move(_e)); });"
  From "conslist.h".

Crane Extraction "boxed_element_drain" BoxedElementDrain.
