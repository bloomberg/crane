From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A module type naming a mapped container of an element that recurses
    through it, under a [Boxed Element] wrapper: the module's struct holds
    [crane::list<crane::box<rose>>], so the concept the module type becomes
    has to ask for that type too, the element hole decided as everywhere
    else, or the module satisfying the module type does not satisfy the
    concept: [children]'s result is asked for by [std::same_as]. *)
Module BoxedElementConcept.

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

Module Type FOREST.
  Parameter forest : list rose.
  Parameter count : list rose -> nat.
  Parameter children : rose -> list rose.
End FOREST.

Module Forest <: FOREST.
  Definition forest : list rose := [Node 1 []; Node 2 [Node 3 []]].
  Definition count (l : list rose) : nat := fold_left (fun n r => n + size r) l 0.
  Definition children (r : rose) : list rose := match r with Node _ ks => ks end.
End Forest.

Module Measure (F : FOREST).
  Definition total : nat := F.count F.forest + F.count (flat_map F.children F.forest).
End Measure.

Module M := Measure Forest.

Definition total : nat := M.total.

End BoxedElementConcept.

Crane Extract Inductive list =>
  "crane::list<%elem>"
  [ "crane::list<%elem>{}"
    "crane::cons(%a0, %a1)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.tail(); %br1 }"
  Boxed Element "crane::box<%t0>"
  From "conslist.h".

Crane Extraction "boxed_element_concept" BoxedElementConcept.
