From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List. Import ListNotations.
(** Using [nth_error] on a [list (nat -> nat)] instantiates the
    erasure-converting [List] constructor, whose body names the source
    instantiation's constructor structs.  Because [list] is not merged into
    its [List] wrapper struct, those names are dependent and must be spelled
    [typename List::template list<_U>::Nil]. *)

Module ListErasureCtorTypename.
Definition pick (n : nat) : option (nat -> nat) :=
  nth_error [fun k => k + 1; fun k => k * 2] n.
Definition go : nat := match pick 1 with Some f => f 21 | None => 0 end.
End ListErasureCtorTypename.
Crane Extraction "list_erasure_ctor_typename" ListErasureCtorTypename.
