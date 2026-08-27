From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List. Import ListNotations.
(** WIP: Using `nth_error` on a `list (nat -> nat)` emits the erasure-converting
    `List` constructor with a doubled qualifier
    (`typename List::typename List::template list<_U>::Nil`), which is not even
    syntactically valid C++. *)

Module ListErasureCtorTypename.
Definition pick (n : nat) : option (nat -> nat) :=
  nth_error [fun k => k + 1; fun k => k * 2] n.
Definition go : nat := match pick 1 with Some f => f 21 | None => 0 end.
End ListErasureCtorTypename.
Crane Extraction "list_erasure_ctor_typename" ListErasureCtorTypename.
