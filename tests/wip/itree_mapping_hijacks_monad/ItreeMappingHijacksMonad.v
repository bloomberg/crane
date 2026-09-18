(** Crane bug: importing [Monads.ITreeReified] makes *every* [Monad] instance
    extract to the ITree one.

    [Err] is an ordinary user-defined monad with its own instance.  With
    [Monads.ITreeReified] in scope, its [bind] and [ret] are emitted as
    [itree_bind] and [itree_ret]:

      Err<Nat> twice(const Err<Nat> &x) {
        return itree_bind(x, [=](const Nat &a) mutable {
          return itree_bind(
              x, [=](const Nat &b) mutable { return itree_ret(a.add(b)); });
        });
      }

    Removing the [Monads.ITreeReified] import makes this extract correctly, so
    the mapping is being applied by monad-ness rather than by carrier.

    Expected: [Monad_Err::bind] / [Monad_Err::ret], as without the import.
    Actual:   error: no matching function for call to 'itree_bind'

    Seen in Vellvm 67 times as "no viable conversion from returned value of
    type 'std::shared_ptr<ITree<X>>' to function return type 'EOU<X>'":
    [EOU] is Vellvm's own error monad, and every [ret] in it becomes
    [itree_ret]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monads.
Import MonadNotation.
Open Scope monad_scope.

(* A monad of the user's own, alongside the reified ITree one. *)
Variant Err (X : Type) : Type := Ok (x : X) | Bad.
Arguments Ok {X}.
Arguments Bad {X}.

#[global] Instance Monad_Err : Monad Err :=
  {| ret := fun _ x => Ok x
   ; bind := fun _ _ c k => match c with Ok x => k x | Bad => Bad end |}.

Definition twice (x : Err nat) : Err nat := a <- x ;; b <- x ;; ret (a + b).

Module ItreeMappingHijacksMonad.
  Definition use (n : nat) : Err nat := twice (Ok n).
End ItreeMappingHijacksMonad.

Crane Extraction "itree_mapping_hijacks_monad" ItreeMappingHijacksMonad.
