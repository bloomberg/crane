(** Found by Ephyra round 25. Variant of round 15's
    [local_fix_alias_function_result]: a local fixpoint whose result is a
    function type ending in a function-type alias ([nat -> st nat], with
    [st A := nat -> A * nat]) and whose accumulator has that type, passed on
    through an [if] that joins a lambda with the accumulator. The generated
    C++ was right, but the typed-fit check found an [st nat] value stored in
    a destination typed [nat * nat]: the [if], an argument of the local
    fixpoint's self-call, was built at the enclosing function's result
    [st nat], so its lambda branch returned into that type's pair.

    Fixed: an argument of a call of a local function is generated with the
    parameter's declared type, not the enclosing function's result, as the
    return type in force, and a match there is built at it
    ([Application.eta_fun], a non-global callee), as for a global callee. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
Import ListNotations.

Module LocalFixAliasAccJoin.

Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).

Definition result : nat :=
  let f := let fix go (l : list nat) (acc : nat -> st nat) {struct l} : nat -> st nat :=
             match l with
             | [] => fun _ => sret 7
             | _ :: rest => go rest (if Nat.leb 12 0 then (fun _ => sret 1) else acc)
             end
           in go [] (fun _ => sret 2) in
  fst (f 0 3).

End LocalFixAliasAccJoin.

Crane Extraction "local_fix_alias_acc_join" LocalFixAliasAccJoin.
