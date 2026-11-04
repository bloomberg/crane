From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A [Boxed Element] container whose constructors are [%result] blocks.

    A block's text is spliced as statements, and its [%elem] hole is decided
    like a constructor template's: boxed where the element recurses through
    the container, so [list rose] builds [crane::list<crane::box<rose>>]
    while [list nat] builds [crane::list<uint64_t>]. *)
Module BoxedElementBlockTemplate.

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

Definition leaves (r : rose) : list nat :=
  match r with Node n ks => n :: map (fun k => match k with Node m _ => m end) ks end.

Definition sample : rose := Node 1 [Node 2 []; Node 3 [Node 4 []]; Node 5 []].

Definition sample_total : nat := total sample.
Definition sample_leaves : list nat := leaves sample.

End BoxedElementBlockTemplate.

Crane Extract Inductive list =>
  "crane::list<%elem>"
  [ "%result = crane::list<%elem>{};"
    "%result = crane::cons(%a0, %a1);" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.tail(); %br1 }"
  Boxed Element "crane::box<%t0>"
  From "conslist.h".

Crane Extraction "boxed_element_block_template" BoxedElementBlockTemplate.
