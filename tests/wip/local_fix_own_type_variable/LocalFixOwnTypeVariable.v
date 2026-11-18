From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** A local fixpoint with a type binder of its own, [let fix go {B}], inside
    a definition polymorphic in [A]: Local_types.settle mints [go]'s open
    variables from [1], so [B] is numbered [T1], the number of [A], and
    lowering reads it as [A].  [f]'s [go] takes [const List<T1> &l] and is
    passed a [List<pt>], which does not convert to [List<uint64_t>].

    Minting past the definition's variables ([outer + 1]) lifts [go] over
    [T1] and its own [T2] and fixes [f], but breaks [h]: the type of [go]'s
    [x : B] is a metavariable nothing in the body solves (the declared type
    binds [C] of its own, so extraction does not unify it), minted as a
    third variable rather than [B]; numbered from [1] it lands on [B] by
    coincidence.  The binder needs its declared type first. *)
Module LocalFixOwnTypeVariable.

Record pt : Type := mkpt { px : nat; py : bool }.

Definition f {A : Type} (a : A) : nat :=
  let fix go {B : Type} (l : list B) (acc : list A) {struct l} : nat :=
    match l with [] => length acc | _ :: r => go r (a :: acc) end in
  go [mkpt 1 true; mkpt 2 false] [a].

Definition t : nat := f 7.

Definition h {A B : Type} (a : A) (b : B) : nat :=
  let fix go {C : Type} (l : list C) (x : B) {struct l} : nat :=
    match l with [] => 0 | _ :: r => S (go r x) end in
  go [a; a] b + go [b] b + go [true] b.

Definition v : nat := h 1 false.

End LocalFixOwnTypeVariable.

Crane Extraction "local_fix_own_type_variable" LocalFixOwnTypeVariable.
