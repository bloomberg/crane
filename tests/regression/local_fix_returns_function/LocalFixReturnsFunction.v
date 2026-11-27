From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A local [let fix go ... : nat -> nat] applied to one more argument than it
    binds.  The C++ lambda for [go] is eta-expanded to return [uint64_t], but its
    branches still return lambdas, and the recursive call names [go] inside its
    own [auto] initializer.  Under CRANE_CHECK_IR=1 (the test suite) extraction
    stops first: "closure escape: the local fixpoint go escapes in its
    generated code but nowhere in Core". *)
Module LocalFixReturnsFunction.

Definition t (l : list nat) : nat :=
  (fun w : nat -> nat => w 1)
  (let fix go (l : list nat) (acc : nat -> nat) {struct l} : nat -> nat :=
     match l with [] => (fun x => x + 1) | _ :: r => go r acc end in go l (fun x => x)).

(** The same fixpoint at top level, applied to fewer arguments than it
    binds once eta-expansion gives it the definition's last parameter: the
    closure for the partial application passed the written arguments last
    first, [go(acc, l, _pa0)], which does not compile for [g] and swaps
    [l] and [acc] for [h]. *)
Definition g (n : nat) : option nat -> option nat :=
  let fix go (l : list bool) (acc : option nat -> option nat) {struct l} : option nat -> option nat :=
    match l with [] => (fun _ => None) | _ :: r => go r acc end in go [] (fun _ => None).

Definition h (n : nat) : option nat -> option nat :=
  let fix go (l : list bool) (acc : nat) {struct l} : option nat -> option nat :=
    match l with
    | [] => (fun x => match x with Some y => Some (y + acc) | None => Some acc end)
    | _ :: r => go r (S acc)
    end in go [true] n.

End LocalFixReturnsFunction.

Crane Extraction "local_fix_returns_function" LocalFixReturnsFunction.
