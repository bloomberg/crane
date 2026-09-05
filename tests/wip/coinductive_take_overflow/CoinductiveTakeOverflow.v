From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Set Crane Loopify.

Module CoinductiveTakeOverflow.

(** Taking a long prefix of a lazily forced stream.  Two [Cons] constructors
    are in play -- this stream's and [list]'s -- and the loopified [take]
    writes into the tail field of the latter, so the constructor field names
    have to stay told apart by their owning inductive. *)
CoInductive stream (A : Type) : Type := Cons : A -> stream A -> stream A.
Arguments Cons {A}.

CoFixpoint from (n : nat) : stream nat := Cons n (from (S n)).

CoFixpoint smap {A B : Type} (f : A -> B) (s : stream A) : stream B :=
  match s with Cons x rest => Cons (f x) (smap f rest) end.

Fixpoint take {A : Type} (n : nat) (s : stream A) : list A :=
  match n with
  | O => []
  | S k => match s with Cons x rest => x :: take k rest end
  end.

Definition total : nat :=
  fold_left Nat.add (take 50000 (smap (fun n => n * 2) (from 0))) 0.

End CoinductiveTakeOverflow.
Crane Extraction "coinductive_take_overflow" CoinductiveTakeOverflow.
