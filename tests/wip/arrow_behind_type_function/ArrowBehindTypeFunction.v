(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a function type that is an arrow only after a definition
    unfolds -- an alias [cont R A := (A -> R) -> R], or a type computed by
    recursion such as [nfun n] -- is spelled with the wrong arity where a
    lambda meets it.
    - [callcc]'s argument is a function taking [esc : A -> cont R B].  The
      lambda passed to it declares [esc] flat, as
      [crane::fn<R(A, crane::fn<R(B)>)>], while [callcc]'s parameter
      expects it curried, as [crane::fn<cont<R, B>(A)>]: no matching call.
    - A two-argument lambda passed at [nfun 2] is erased flat,
      [crane_erase_fn([](uint64_t, uint64_t) ...)], and read back curried,
      as a one-argument [crane::fn] returning another: [std::bad_any_cast]
      at run time. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ArrowBehindTypeFunction.

Definition cont (R A : Type) := (A -> R) -> R.
Definition cret {R A} (a : A) : cont R A := fun k => k a.
Definition cbind {R A B} (m : cont R A) (f : A -> cont R B) : cont R B :=
  fun k => m (fun a => f a k).
Definition callcc {R A B} (f : (A -> cont R B) -> cont R A) : cont R A :=
  fun k => f (fun a _ => k a) k.

Definition escaped : nat :=
  callcc (fun (esc : nat -> cont nat nat) => cbind (esc 5) (fun _ => cret 100))
    (fun x => x * 2).

Fixpoint nfun (n : nat) : Type := match n with 0 => nat | S m => nat -> nfun m end.

Fixpoint applyl (n : nat) : nfun n -> list nat -> nat :=
  match n return nfun n -> list nat -> nat with
  | 0 => fun v _ => v
  | S m => fun f l => match l with [] => applyl m (f 0) [] | x :: t => applyl m (f x) t end
  end.

Definition product : nat := applyl 2 (fun a b => a * b) [3; 4].

End ArrowBehindTypeFunction.

Crane Extraction "arrow_behind_type_function" ArrowBehindTypeFunction.
