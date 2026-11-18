From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Memory safety: use after return.  A corecursive branch builds a local
    fixpoint lambda [go] that captures [m] (a local of [h]) by reference, then
    returns [stream::lazy_([=] { return go(...); })].  The thunk copies [go]
    but not what it refers to; when it is forced after [h] returned, [m] is a
    dead stack slot, so [h(m)] recurses on garbage (the test runs away in time
    and memory).  CRANE_CHECK_IR=1 reported it first: "closure captures: the
    local fixpoint lambda go reads its scope by reference and escapes it".
    Escape analysis now counts what the value of a body suspended whole names,
    and what a suspended constructor's arguments name, as escaping, so [go]
    holds copies. *)
Module CofixThunkDanglingCapture.

CoInductive stream : Type := SCons : nat -> stream -> stream.
CoFixpoint sconst (n : nat) : stream := SCons n (sconst n).

Fixpoint h (n : nat) : stream :=
  match n with
  | O => sconst 0
  | S m => let fix go (l : list nat) (acc : stream) {struct l} : stream :=
             match l with [] => h m | _ :: r => go r acc end in
           go [1; 2] (match n with O => h m | S _ => sconst 2 end)
  end.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.

(** Nested local fixpoints, the inner returning the outer's accumulator. *)
Fixpoint g2 (t : tree) : stream :=
  match t with
  | Leaf => sconst 0
  | Node tl _ _ =>
    let fix go7 (l : list nat) (acc9 : stream) {struct l} : stream :=
      match l with
      | [] => g2 tl
      | _ :: _ =>
        let fix go12 (l2 : list (option nat)) (acc14 : stream) {struct l2} : stream :=
          match l2 with [] => acc9 | _ :: r => go12 r (sconst 0) end in
        go12 [] (sconst 0)
      end in
    go7 [] (sconst 0)
  end.

Fixpoint stake (k : nat) (s : stream) : list nat :=
  match k with O => [] | S k' => match s with SCons x r => x :: stake k' r end end.

Definition t : nat := fold_left Nat.add (stake 3 (h 3)) 0.

Definition t2 : nat := fold_left Nat.add (stake 3 (g2 (Node (Node Leaf 1 Leaf) 2 Leaf))) 0.

End CofixThunkDanglingCapture.

Crane Extraction "cofix_thunk_dangling_capture" CofixThunkDanglingCapture.
