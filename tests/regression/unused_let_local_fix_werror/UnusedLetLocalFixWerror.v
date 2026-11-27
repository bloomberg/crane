From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A let bound to a local fixpoint's result, read only in the never-taken
    recursive arm of another local fixpoint that is called on [[]]: the arm is
    dropped but the binding is kept, "variable 'x' set but not used" under
    -Werror.  The value is right.  [go2]'s loop drops its unread [acc], and
    with it the only read of [x]; the declaration and the assignment of the
    choice [x]'s value was lowered to stayed.  Simplify now drops a local
    declared without a value that nothing reads, with the pure values,
    choices among them included, assigned to it.  [g] assigns [x] in a
    mapped match on [nat], and [y] alongside; [h] assigns [x] a call, which
    is kept as a statement. *)
Module UnusedLetLocalFixWerror.

Definition f (s : nat) : nat :=
  let x := (let fix go (l : list nat) (acc : nat) {struct l} : nat :=
              match l with [] => 0 | _ :: _ => 7 end in go [] 0) in
  let fix go2 (l : list bool) (acc : nat) {struct l} : nat :=
    match l with [] => 0 | _ :: r => go2 r x end in go2 [] 8.

Definition g (s : nat) : nat :=
  let x := match s with O => 1 | S _ => 2 end in
  let y := (let fix go (l : list nat) (acc : nat) {struct l} : nat :=
              match l with [] => acc | _ :: _ => 7 end in go [] s) in
  let fix go2 (l : list bool) (a b : nat) {struct l} : nat :=
    match l with [] => 3 | _ :: r => go2 r x y end in go2 [] 8 9.

Definition h (s : nat) : nat :=
  let x := (let fix go (l : list nat) (acc : nat) {struct l} : nat :=
              match l with [] => acc | n :: r => go r (n + acc) end in go [1; 2] s) in
  let fix go2 (l : list bool) (acc : nat) {struct l} : nat :=
    match l with [] => 4 | _ :: r => go2 r x end in go2 [] 8.

End UnusedLetLocalFixWerror.

Crane Extraction "unused_let_local_fix_werror" UnusedLetLocalFixWerror.
