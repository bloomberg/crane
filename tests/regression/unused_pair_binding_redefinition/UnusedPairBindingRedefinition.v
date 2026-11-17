From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Two sequential matches on pairs whose fields are unused, each scrutinee a
    local fixpoint call, lower to two [auto [_x, _x0] = ...;] structured
    bindings in one scope: "redefinition of '_x'".  [g] is the same with the
    fields read: "redefinition of 'p'".  The let's body now avoids the names
    its value's statements declare in the shared scope. *)
Module UnusedPairBindingRedefinition.

Definition f (a : nat) : nat :=
  let x := match (let fix go (l : list nat) (acc : nat * nat) {struct l} : nat * nat :=
                    match l with [] => acc | _ :: _ => (a, a) end in go [0; 0] (a, a))
           with (p, q) => 0 end in
  match (let fix go2 (l : list nat) (acc : bool * bool) {struct l} : bool * bool :=
           match l with [] => (true, true) | _ :: _ => acc end in go2 [a; a] (true, true))
  with (p, q) => x + 5 end.

Definition g (a : nat) : nat :=
  let x := match (let fix go (l : list nat) (acc : nat * nat) {struct l} : nat * nat :=
                    match l with [] => acc | _ :: _ => (a, a) end in go [0; 0] (a, a))
           with (p, q) => p end in
  match (let fix go2 (l : list nat) (acc : nat * nat) {struct l} : nat * nat :=
           match l with [] => (1, 2) | _ :: _ => acc end in go2 [a; a] (3, 4))
  with (p, q) => x + p + q end.

End UnusedPairBindingRedefinition.

Crane Extraction "unused_pair_binding_redefinition" UnusedPairBindingRedefinition.
