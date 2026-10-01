(** Crane bug: a [bind] nested inside another [bind]'s continuation is emitted
    with an empty first template argument -- the Monad instance is resolved to
    nothing.

    [g] is [itree_poly_event_arg]'s program with a second [bind].  The outer
    one is mapped correctly to [itree_bind]; the inner one falls back to the
    generic [Monad0::bind], whose first template parameter is the instance,
    and that instance prints as nothing:

      template <Monad _tcI0, typename T2, typename T3, typename F1>
      static typename _tcI0::template m<T3> bind(...);
      ...
      return itree_bind(x, [=](const Nat &a) mutable {
        return Monad0::template bind<, Nat, Nat>(x, [=](const Nat &b) mutable {
                                    ^^ the instance is missing
          return Monad0::template ret<, Nat>(a.add(b));
        });
      });

    A [Monad] instance that is a class *parameter* comes out right --
    [Monad0::template bind<_tcI0, Nat, Nat>] -- so this is specific to the
    instance supplied by [Monads.ITreeReified].

    Expected: the outer and the inner [bind] to be spelled the same way.
    Actual:   error: expected expression

    Seen in Vellvm 273 times: 160 [bind<,], 87 [ret<,], 16 [map_monad<,], and
    a tail of [fmap<,], [loop_monad<,], [interp<,], [interp_state<,]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monads.
Import MonadNotation.
Open Scope monad_scope.

Definition g {E : Type -> Type} (x : itree E nat) : itree E nat :=
  a <- x ;; b <- x ;; ret (a + b).

Module ItreeNestedBindInstance.
  Definition use (n : nat) : itree void1 nat := g (Ret n).
End ItreeNestedBindInstance.

Crane Extraction "itree_nested_bind_instance" ItreeNestedBindInstance.
