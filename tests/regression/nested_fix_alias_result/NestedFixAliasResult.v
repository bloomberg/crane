(** Found by Ephyra (round 22). A variant left by the fix of round 15's
    [local_fix_alias_function_result]: a local fixpoint whose result is the
    state monad [st nat] (a function type behind a definition), defined and
    called inside the base case of another such fixpoint.

    Expected: compiles; [result = 4].

    Fixed: compile error "no matching function for call to object of type
    '(lambda ...)'": the outer fixpoint, inlined and eta-expanded with the
    state argument [eta0_], passed it on as
    [inner(nil, std::move(acc), eta0_)], but [inner] is generated with two
    parameters returning [st<uint64_t>].  An applied local fixpoint was
    called with every argument at once; arguments past its lambda's
    parameters now apply to what it returns
    ([inner(nil, std::move(acc))(eta0_)]), as at any call of a known
    arity. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.
From Crane Require Extraction.
From Stdlib Require Import List.
From Corelib Require Import PrimString.
Import ListNotations.
Module NestedFixAliasResult.
Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).
Definition f1 : st nat :=
  let fix outer (l : list bool) (acc : st nat) {struct l} : st nat :=
    match l with
    | [] =>
      let fix inner (m : list nat) (acc2 : st nat) {struct m} : st nat :=
        match m with [] => acc2 | _ :: rest => let r := inner rest acc2 in r end in
      inner [] acc
    | _ :: _ => sret 0
    end in
  outer [] (sret 4).
Definition result : nat := fst (f1 0).
End NestedFixAliasResult.
Crane Extraction "nested_fix_alias_result" NestedFixAliasResult.
