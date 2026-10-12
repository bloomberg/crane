(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a rank-2 callback whose type mentions a type family, passed to
    a callee that keeps it as a [crane::fn] -- here because a local fixpoint
    captures it -- gets an adapter of the wrong signature, and the callee's
    body casts the callback's result to the wrong type.
    - [both] declares [g] as [crane::fn<T1(crane::obj, List<crane::obj>, T1)>],
      erased only where the family is; the caller builds the fully erased
      [crane_erase_fn<crane::obj>] adapter, a
      [crane::fn<crane::obj(crane::obj, crane::obj, crane::obj)>], which does
      not convert: "no matching function for call to 'both'".
    - Inside [both], the local fixpoint casts [g]'s result to the enclosing
      function's return type [std::pair<T1, T1>] rather than to the
      fixpoint's own [T1].
    A callee that deduces the callback works
    ([regression/rank2_family_argument_adapter]). *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module Rank2CallbackKeptAsFn.

Definition both (P : forall A : Type, list A -> Type) (f : forall A, P A [])
  (g : forall A x (t : list A), P A t -> P A (x :: t)) (A : Type) (l : list A) : P A l * P A l :=
  let go := fix F (m : list A) : P A m := match m with [] => f A | x :: t => g A x t (F t) end in
  (go l, go l).

Definition len (A : Type) (l : list A) : nat :=
  fst (both (fun _ _ => nat) (fun _ => 0) (fun _ _ _ k => S k) A l).

Definition result : nat := len bool [true; false; true].

End Rank2CallbackKeptAsFn.

Crane Extraction "rank2_callback_kept_as_fn" Rank2CallbackKeptAsFn.
