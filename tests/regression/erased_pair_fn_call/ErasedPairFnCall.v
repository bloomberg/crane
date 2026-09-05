From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module ErasedPairFnCall.

(** The consumer side of an erased pair: a function read back out of an
    erased field is applied directly, without the [any_cast] that would
    recover its call operator. *)
Definition boxed := sigT (fun A : Type => (list A * (list A -> nat))%type).

Definition mk {A : Type} (l : list A) : boxed := existT _ A (l, @length A).

Definition size (b : boxed) : nat := match b with existT _ _ (l, f) => f l end.

Definition items : list boxed := [ mk [1;2;3]; mk [true;false]; mk ([] : list nat) ].

Definition total : nat := fold_left (fun acc b => acc + size b) items 0.

End ErasedPairFnCall.
Crane Extraction "erased_pair_fn_call" ErasedPairFnCall.
