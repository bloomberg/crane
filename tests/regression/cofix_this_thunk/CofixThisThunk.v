From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** BUG HYPOTHESIS: replace_return_this_expr converts CPPthis to
    shared_from_this() for CPPfun_call arguments but NOT for
    CPPmethod_call receivers (falls through | e -> e). When a cofixpoint
    is methodified on a coinductive type and its body calls another
    methodified function on [this], the raw [this] pointer is captured in
    the lazy thunk via [=, this]. If the caller's shared_ptr to the input
    stream is a temporary destroyed before the thunk is forced, the raw
    [this] dangles.

    For the bug to trigger, the module must be EPONYMOUS with the
    coinductive type (matching names) so that functions get methodified
    as instance methods on the type. *)

(** Module name "Sseq" matches coinductive "sseq" -> eponymous *)
Module Sseq.

CoInductive sseq (A : Type) := SCons { shead : A; stail : sseq A }.
Arguments SCons {A}.
Arguments shead {A}.
Arguments stail {A}.

(** This will be methodified on sseq because first arg is sseq A
    and the module is eponymous. *)
Definition double_head {A : Type} (s : sseq A) (f : A -> A) : A :=
  f (shead s).

(** Cofixpoint also methodified on sseq. Body calls double_head on
    the first arg WITHOUT destructuring via match. This creates
    this->double_head(f) inside the lazy thunk. *)
CoFixpoint smap {A : Type} (s : sseq A) (f : A -> A) : sseq A :=
  SCons (double_head s f) (smap (stail s) f).

(** Direct shead access variant — uses the record projection directly
    in the cofixpoint body *)
CoFixpoint smap_direct {A : Type} (s : sseq A) (f : A -> A) : sseq A :=
  SCons (f (shead s)) (smap_direct (stail s) f).

(** Counting sequence *)
CoFixpoint nats_from (n : nat) : sseq nat :=
  SCons n (nats_from (S n)).

(** Take n elements *)
Fixpoint take {A : Type} (n : nat) (s : sseq A) : list A :=
  match n with
  | O => nil
  | S m => shead s :: take m (stail s)
  end.

(** Sum of a list *)
Fixpoint sum (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: xs => x + sum xs
  end.

(** test1: smap (nats_from 0) S gives [1, 2, 3, 4, ...]
    take 4 -> [1, 2, 3, 4] -> sum = 10 *)
Definition test1 : nat :=
  let s := smap (nats_from 0) S in
  sum (take 4 s).

(** test2: smap_direct (nats_from 0) S gives [1, 2, 3, 4, ...]
    take 4 -> [1, 2, 3, 4] -> sum = 10 *)
Definition test2 : nat :=
  let s := smap_direct (nats_from 0) S in
  sum (take 4 s).

End Sseq.

Crane Extraction "cofix_this_thunk" Sseq.
