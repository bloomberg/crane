(** Crane bug: a call whose result is monadic only through a *generic* monad is
    wrapped in [ret] a second time.

    [map_monad] is generic over [Monad m], so its ML result type is [m (list
    B)] with [m] a type variable.  Passing it to [ITree.bind] emits:

      return itree_bind([&]() -> std::shared_ptr<ITree<List<tree>>> {
        return ITree<List<tree>>::ret(
          map_monad<Monad_itree<std::any>, tree, tree>(...));
      }(), ...)

      error: no viable conversion from
        'typename Monad_itree<std::any>::template m<List<tree>>'
        (aka 'std::shared_ptr<ITree<List<tree>>>') to 'List<tree>'

    [map_monad]'s own declaration is right -- it returns [typename
    _tcI0::template m<List<T3>>] -- so the value handed to [ret] is already a
    tree, and [ret] wants the thing a tree carries.

    The gate is [is_reified_monadic_expr], which asks whether the callee's ML
    result type is monadic.  Every test it makes is against a concrete monad
    glob, and here the result is an application of the class's own type
    variable: the monad is known at the call site (the emitted instance
    argument is [Monad_itree<std::any>]) and unknown in the callee's type.  So
    the argument is judged not-yet-a-tree and lifted, and the lift is what does
    not compile.

    Not reachable through a monad that is concrete in the callee's type, which
    is why the existing reified-itree tests do not show it: [itree_ret_go] and
    [itree_nested_bind_instance] both name [itree] in the callee.

    Reduced from the Vellvm session's [axiom_itree_eta_lam] and
    [axiom_section_context_eta], which are the same single defect reached two
    ways.  Not itself present in Vellvm. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From Stdlib Require Import List.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monad.
Import ListNotations.

Variant E1 : Type -> Type := e1 : E1 nat.

Module GenericMonadResultRewrapped.

  (** Generic over [Monad m]: the result type is an application of a type
      variable, which is what the reification gate cannot read. *)
  Fixpoint map_monad {m : Type -> Type} `{Monad m} {A B : Type}
      (f : A -> m B) (l : list A) : m (list B) :=
    match l with
    | [] => ret []
    | x :: xs =>
      bind (f x) (fun y => bind (map_monad f xs) (fun ys => ret (y :: ys)))
    end.

  Definition twice {E} (n : nat) : itree E nat := Ret (n + n).

  (** The first argument of [ITree.bind] is a generic-monad call result, so it
      is already a tree and must not be lifted again. *)
  Definition run {E} (l : list nat) : itree E (list nat) :=
    ITree.bind (map_monad twice l) (fun ys => Ret ys).

  Definition go (l : list nat) : itree E1 (list nat) := run l.

End GenericMonadResultRewrapped.

Crane Extraction "generic_monad_result_rewrapped" GenericMonadResultRewrapped.
