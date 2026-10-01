(** Crane bug: a function polymorphic in the event type emits a callee with no
    name at all, and leaks the erased event index as a template parameter it
    then applies to two arguments.

    [f] is [ItreeRetGo]'s program with [E] left free.  The reified backend
    erases the event index -- [itree E R] is [ITree<R>] whatever [E] is -- so
    [E] should not reach the C++ signature.  Instead it becomes [T1], and the
    [Ret] call site loses its callee:

      template <typename T1>
      std::shared_ptr<ITree<Nat>> f(const std::shared_ptr<ITree<Nat>> &x) {
        return itree_bind(x, [](Nat a) {
          return std::shared_ptr<ITree<std::any>>::go(
              <T1<std::any, std::any>, Nat, std::shared_ptr<ITree<Nat>>>(
                  std::any(Nat::s(a))));
        });
      }

    Three things are wrong on that one call: the name before [<] is missing,
    [T1] is declared as a plain [typename] but applied as a template, and it
    is applied to two arguments where the event index takes one.

    Expected: no [T1] parameter at all, and the [Ret] to be spelled the way it
              is in [itree_ret_go].
    Actual:   error: expected expression
              error: 'Nat' does not refer to a value
              error: expected '(' for function-style cast or type construction
              (plus the [itree_ret_go] errors, which this also shows)

    Seen in Vellvm as 251 x "expected expression" and 159 x "use of undeclared
    identifier", the two largest clusters; the leaked parameter appears as
    [MonadIter<T1>] and [_default_nan_64_F<T1>] with [T1] never declared. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monads.
Import MonadNotation.
Open Scope monad_scope.

Definition f {E : Type -> Type} (x : itree E nat) : itree E nat :=
  a <- x ;; Ret (S a).

Module ItreePolyEventArg.
  Definition use (n : nat) : itree void1 nat := f (Ret n).
End ItreePolyEventArg.

Crane Extraction "itree_poly_event_arg" ItreePolyEventArg.
