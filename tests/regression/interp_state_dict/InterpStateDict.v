(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From ITree Require Import ITree Events.State.
Require Crane.Extraction.
Require Import Crane.Mapping.NatIntStd.

(** A counter interpreted through coq-itree's [interp_state].

    Fixed: the call wrote [State::interp_state<MonadIter_itree,
    Monad_itree, ...>], and clang rejected the bare [MonadIter_itree] for
    the [MonadIter]-concept parameter: the instance's struct takes the
    event family as a template parameter, and the use's argument for it
    ([void1]) is erased, which dropped the whole argument list.  An
    instance's struct is never named without its arguments, so an erased
    one is written as the box ([MonadIter_itree<crane::obj>]). *)
Module InterpStateDict.

Variant cnt : Type -> Type := Tick : cnt unit | Get : cnt nat.

Definition handle : cnt ~> Monads.stateT nat (itree void1) :=
  fun _ e s =>
    match e with
    | Tick => Ret (S s, tt)
    | Get => Ret (s, s)
    end.

Fixpoint ticks (n : nat) : itree cnt unit :=
  match n with
  | 0 => Ret tt
  | S m => ITree.bind (trigger Tick) (fun _ => ticks m)
  end.

Definition prog (n : nat) : itree cnt nat :=
  ITree.bind (ticks n) (fun _ => trigger Get).

Definition run (n : nat) : itree void1 (nat * nat) :=
  interp_state handle (prog n) 0.

End InterpStateDict.

Crane Extraction "interp_state_dict" InterpStateDict.
