(** Crane bug: under two state transformers, the tree a body returns is
    built at the outer transformer's pair, and the value is applied to both
    its arguments at once.

    [stacked : stateT nat (stateT bool (itree noE)) nat] is
    [nat -> bool -> itree noE (bool * (nat * nat))].
    Observed (e3703bf80, and after the synthesised templates are planned):
      static inline const stateT<Nat, crane_carrier_tc_f7ac3d5701e8f328, Nat>
          stacked = []() {
            return [](Nat n) {
              return [=](bool b) {
                return Itree<noE, std::pair<Nat, Nat>>::go(
                    ItreeF<noE, std::pair<Nat, Nat>, ...>::retf(
                        std::make_pair(!(b), std::make_pair(n + 1, n))));
      ...
      stacked(Nat::s(...), true).observe();
    Diagnostics:
      error: no viable conversion from 'pair<bool, std::pair<Nat, Nat>>'
             to 'pair<Nat, Nat>'
      error: no matching function for call to object of type 'const
             stateT<Nat, crane_carrier_tc_f7ac3d5701e8f328, Nat>'
    Expected: the tree built at [std::pair<bool, std::pair<Nat, Nat>>], and
    [stacked(...)(true)]. *)

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
