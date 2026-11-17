(** A [bind] continuation's binder, in a body generic in its monad, is typed
    at the element the monadic argument carries, not at the monad.

    [map_monad_acc] is Vellvm's [ListUtil.map_monad_acc], in a section over
    a monad [m].  Nothing names the type of [b] or of the accumulator but
    [bind]'s instantiation: [bind : m A -> (A -> m B) -> m B] applied to
    [f a : m T].  Extraction instantiates [bind]'s [m] with a metavariable,
    and [m A] stands for an unknown of its own while the head is unsolved;
    the dictionary never names the carrier, so the unknown was unified with
    [m T] and [A] was left open.  The local fixpoint's variables are then
    minted from 1 ({!Core_passes.Local_types}), where the declaration's own
    variable 1 is [m]: the accumulator was a [List<typename _tcI0::m>].
    Reading [m A] unified with [m T] as [A = T] gives it [List<T3>]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
From ExtLib Require Import Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

Inductive EOU (A : Type) : Type :=
| Ok : A -> EOU A
| Err : nat -> EOU A.

Arguments Ok {A}.
Arguments Err {A}.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := fun _ a => Ok a
   ; bind := fun _ _ m k => match m with Ok a => k a | Err c => Err c end
  |}.

Module BindContinuationMonadElement.
Section monad.
  Variable m : Type -> Type.
  Variable M : Monad m.

  Definition map_monad_acc {A B} (f : A -> m B) (l : list A) : m (list B) :=
    (fix loop acc l :=
       match l with
       | nil => ret (rev_append acc nil)
       | cons a l' => b <- f a;; loop (cons b acc) l'
       end) nil l.
End monad.

Definition run : EOU (list bool) :=
  map_monad_acc EOU EOU_monad (fun n => Ok (Nat.even n)) (cons 1 (cons 2 nil)).
End BindContinuationMonadElement.
Crane Extraction "bind_continuation_monad_element" BindContinuationMonadElement.
