(** Crane bug: [stateT S (itree E)] in a *function's result type*, generic
    in the family [E], still writes the carrier as bare [Itree].

    Observed (e0242d8ea, which fixed constants typed through a carrier):
      template <typename T1> static stateT<Nat, Itree, Nat> get_st(Nat n) {
    Diagnostics:
      error: too few template arguments for class template 'Itree'
      error: no matching function for call to 'get_st'
    Expected: the carrier holder for [itree T1 _] (e.g.
    [_crane_carrier_tch<T1>::template c]).  [Itree] is file-scope here (the
    ITree library), unlike partial_app_carrier's nested [box].

    Reduced from Vellvm, whose handlers are typed [stateT global_env (itree E)]
    etc.: [static Monads::template stateT<global_env<...>, Itree, T2>]
    (66 errors on e0242d8ea, plus the 9 'call to non-static member function'
    and probably the 12 'this' capture errors in the same code). *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ITree Require Import ITree.

Module StatetItreeReturn.
  (* ExtLib/ITree's stateT, as Vellvm's handlers use it: [stateT S (itree E)]
     in a function's result type, polymorphic in the family E. *)
  Definition stateT (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (prod S A).

  Definition get_st {E : Type -> Type} (n : nat) : stateT nat (itree E) nat :=
    fun s => Ret (s + n, s).

  Variant noE : Type -> Type := .
  Definition r : itree noE (nat * nat) := get_st 1 2.
  Definition is_three : bool :=
    match observe r with RetF (a, _) => Nat.eqb a 3 | _ => false end.
End StatetItreeReturn.

Crane Extraction "statet_itree_return" StatetItreeReturn.
