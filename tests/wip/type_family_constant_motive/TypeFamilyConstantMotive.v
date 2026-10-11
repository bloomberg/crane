(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a function taking a type family [P : nat -> Type] does not
    compile when it is called at a constant family such as [fun _ => bool].
    The arguments of type [P n] are boxed as [crane::obj] at the call, so the
    callee's template parameter deduces to [crane::obj], and its result is
    returned unconverted from a function declared to return [bool]; the
    callback, a lambda over [bool], is not invocable on [crane::obj] either.
    The standard library's [Nat.max_dec] and [Nat.min_dec] are written
    through [Nat.max_case] this way, so a plain [if Nat.max_dec a b] fails. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module TypeFamilyConstantMotive.

Definition pick (P : nat -> Type) (n m : nat)
  (compat : forall x y, x = y -> P x -> P y) (hl : P n) (hr : P m) : P (max n m) :=
  match Nat.leb m n as b return Nat.leb m n = b -> P (max n m) with
  | true => fun e => compat n _ (eq_sym (Nat.max_l n m (proj1 (Nat.leb_le m n) e))) hl
  | false => fun e =>
      compat m _ (eq_sym (Nat.max_r n m (Nat.lt_le_incl _ _ (proj1 (Nat.leb_gt m n) e)))) hr
  end eq_refl.

Definition larger_is_first (n m : nat) : bool :=
  pick (fun _ => bool) n m (fun _ _ _ b => b) true false.

Definition first : bool := larger_is_first 5 3.

(** The same shape in the standard library. *)
Definition max_is_left : bool := if Nat.max_dec 5 3 then true else false.

End TypeFamilyConstantMotive.

Crane Extraction "type_family_constant_motive" TypeFamilyConstantMotive.
