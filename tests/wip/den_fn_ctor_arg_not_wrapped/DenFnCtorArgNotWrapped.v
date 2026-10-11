(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a function passed to a constructor for a field of type [den t]
    is stored in the field's [std::any] unwrapped.  The consumer reads every
    function-typed [den] value as a [crane::fn<crane::obj(crane::obj)>], so
    producers erase functions through [crane_erase_fn]; a function passed
    to an ordinary function's [den] parameter gets that wrapper, but the
    factory argument [box::box0(S)] does not, and [unbox fb 4] throws
    [std::bad_any_cast]. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module DenFnCtorArgNotWrapped.

Inductive ty := TNat | TFun : ty -> ty -> ty.

Fixpoint den (t : ty) : Type := match t with TNat => nat | TFun a b => den a -> den b end.

Inductive box (t : ty) := Box : den t -> box t.
Arguments Box {t}.

Definition unbox {t} (b : box t) : den t := match b with Box x => x end.

Definition fb : box (TFun TNat TNat) := Box (t := TFun TNat TNat) S.

Definition result : nat := unbox fb 4.

End DenFnCtorArgNotWrapped.

Crane Extraction "den_fn_ctor_arg_not_wrapped" DenFnCtorArgNotWrapped.
