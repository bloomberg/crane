(** A value under two state transformers, built and called.

    [stacked : stateT nat (stateT bool (itree noE)) nat] is
    [nat -> bool -> itree noE (bool * (nat * nat))], written as a [stateT]
    whose carrier is another [stateT].  Its tree is built at
    [std::pair<bool, std::pair<Nat, Nat>>], the pair of the inner
    transformer, and [stacked 4 true] is called one arrow at a time,
    [stacked(...)(true)], as the [stateT] the value is declared at takes
    its arguments.  Applying the inner [stateT] used to fill the [itree]'s
    own placeholder as well, building the tree at the outer pair, and the
    call counted only the arrows written out, none, and passed both
    arguments at once. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module NestedStatetRetType.
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  Variant noE : Type -> Type := .

  Definition stacked : stateT nat (stateT bool (itree noE)) nat :=
    fun n b => Ret (negb b, (n + 1, n)).

  Definition unstacked : nat :=
    match observe (stacked 4 true) with RetF (_, (a, _)) => a | _ => 0 end.
End NestedStatetRetType.

Crane Extraction "nested_statet_ret_type" NestedStatetRetType.
