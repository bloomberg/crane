(** Crane bug: under the reified ITree backend, [Ret] is emitted as a static
    member of [std::shared_ptr], which has no such member, and [itree_bind]'s
    continuation is given a [void] return type.

    This is the smallest ITree program there is -- one [bind] over one [Ret],
    at a concrete event type, inside a module -- and it does not compile.

      return itree_bind(
          [=]() mutable -> std::shared_ptr<ITree<Nat>> {
            return std::shared_ptr<ITree<std::any>>::go(
                (std::any(std::move(n))));
          }(),
          [](Nat a) {
            return std::shared_ptr<ITree<std::any>>::go(
                (std::any(Nat::s(a))));
          });

    Expected: [Ret] to name the reified constructor -- [ITree<T>::ret(...)] or
              whatever the runtime spells it -- and [itree_bind] to accept a
              continuation returning [std::shared_ptr<ITree<T>>].
    Actual:   error: no member named 'go' in 'std::shared_ptr<ITree<std::any>>'
              error: no viable conversion from returned value of type
                     'decltype(k(std::declval<Nat>()))' (aka 'void') to
                     function return type 'std::shared_ptr<ITree<Nat>>'

    Seen in Vellvm as 56 x "no member named 'X' in the global namespace" and a
    large share of the 743 errors in the extracted interpreter; every use of
    the ITree monad goes through this.

    See also [itree_poly_event_arg] and [itree_nested_bind_instance], which add
    one Rocq construct each on top of this one. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.

Module ItreeRetGo.
  Definition use (n : nat) : itree void1 nat :=
    ITree.bind (Ret n) (fun a => Ret (S a)).
End ItreeRetGo.

Crane Extraction "itree_ret_go" ItreeRetGo.
