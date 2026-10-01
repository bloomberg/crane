From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
From ExtLib Require Import Structures.Functor Structures.Monad.
From ITree Require Import ITree Basics.Basics.
Import ListNotations MonadNotation.
Open Scope monad_scope.

(** ITree's [Functor_stateT] is not recursive: its [fmap] calls the
    *inner* functor's [fmap].  With [Set Crane Loopify] it is nevertheless
    loopified, as if that inner call were a self-call: the static method
    [Monads::Functor_stateT<...>::fmap] gets a one-frame [_Enter] stack
    starting with [const Functor_stateT<_tcI0, T1> *_self = this;], and
    [this] in a static member function does not compile ("invalid use of
    'this' outside of a non-static member function").  [Monad_stateT]'s
    [bind] gets the same treatment.

    Found in Vellvm with the global [Set Crane Loopify] (3 of its 59
    errors).  Even where it compiled, a call to another instance's method
    treated as recursion would be a wrong program, not just a slow one. *)

Module LoopifyInnerInstanceCall.

  Variant ev : Type -> Type := Ask : ev nat.

  Import Basics.Monads.
  Definition st : stateT nat (itree ev) nat := fun s => ret (s, 41).

  Definition bumped (_ : unit) : itree ev (nat * nat) :=
    (fmap (fun x => x + 1) st) 5.

  (** 5 is the state, 41 + 1 the value. *)
  Definition check (_ : unit) : itree ev bool :=
    p <- bumped tt ;; ret (Nat.eqb (fst p) 5 && Nat.eqb (snd p) 42)%bool.

End LoopifyInnerInstanceCall.

Set Crane Loopify.
Crane Extraction "loopify_inner_instance_call" LoopifyInnerInstanceCall.
