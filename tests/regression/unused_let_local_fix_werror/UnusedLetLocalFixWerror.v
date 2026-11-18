From Crane Require Import Mapping.NatIntStd.
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
    choices among them included, assigned to it. *)
Module UnusedLetLocalFixWerror.

Definition f (s : nat) : nat :=
  let x := (let fix go (l : list nat) (acc : nat) {struct l} : nat :=
              match l with [] => 0 | _ :: _ => 7 end in go [] 0) in
  let fix go2 (l : list bool) (acc : nat) {struct l} : nat :=
    match l with [] => 0 | _ :: r => go2 r x end in go2 [] 8.

End UnusedLetLocalFixWerror.

Crane Extraction "unused_let_local_fix_werror" UnusedLetLocalFixWerror.
