(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: calling a function-typed [den t] value after a match has
    refined [t] does not cast the call's result back.  In [app], the match
    on [V (TFun TNat TNat) f] makes [f : nat -> nat]; the generated code
    casts [f] out of its [std::any] box to a
    [crane::fn<crane::obj(crane::obj)>] and calls it, and returns the
    [crane::obj] it yields from a function declared to return [uint64_t]:
    "no viable conversion from returned value of type 'crane::obj'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module DenFnResultNotCast.

Inductive ty := TNat | TFun : ty -> ty -> ty.

Fixpoint den (t : ty) : Type := match t with TNat => nat | TFun a b => den a -> den b end.

Inductive val := V : forall t, den t -> val.

Definition app (v : val) (n : nat) : nat :=
  match v with V (TFun TNat TNat) f => f n | _ => 0 end.

Definition result : nat := app (V (TFun TNat TNat) S) 4 + app (V (TFun TNat TNat) (fun x => x * 2)) 4.

End DenFnResultNotCast.

Crane Extraction "den_fn_result_not_cast" DenFnResultNotCast.
