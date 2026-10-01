From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From ExtLib Require Import Structures.Monad.

(** A closure whose only use of a captured/passed value is to read it into a
    freshly built pair or record is exactly as borrowable as one that only
    reads it to call another function with it.  [ret]'s [fun s => ret (s, a)]
    has the same shape as [bind]'s [fun s => k (t s)] -- both read [s] once
    -- but only [bind]'s style used to be recognised as read-only.  The state
    monad below models that: [ret]'s continuation builds a pair from the
    ambient state, and should borrow it exactly as [bind]'s does. *)
Module BorrowConstructionArgument.

  Record big := mkBig { b1 : nat; b2 : nat; b3 : nat; b4 : nat }.

  Definition stateT (a : Type) : Type := big -> (big * a).

  #[export] Instance Monad_stateT : Monad stateT :=
    {| ret _ a := fun s => (s, a)
     ; bind _ _ t k := fun s => let '(s', v) := t s in k v s'
    |}.

  Definition test (a : nat) : stateT nat := ret a.

  Definition run (b : big) : nat * big :=
    let '(s', v) := test 5 b in (v, s').

End BorrowConstructionArgument.

Crane Extraction "borrow_construction_argument" BorrowConstructionArgument.
