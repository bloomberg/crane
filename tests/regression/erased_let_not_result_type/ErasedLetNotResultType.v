(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [let] whose type erasure removes entirely -- a semantic value typed by
    a type its functor parameter computes from a value -- binds a box, which
    is not to be cast to the enclosing function's result.  ParseALot's
    [multistep] threw [bad_any_cast] here. *)

From Stdlib Require Import PeanoNat.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ErasedLetNotResultType.

Module Type SYMS.
  Parameter semty : nat -> Type.
  Parameter cast : forall a b : nat, a = b -> semty a -> semty b.
  Parameter default : forall n, semty n.
  Parameter size : forall n, semty n -> nat.
End SYMS.

Module Parser (S : SYMS).
  Inductive result (x : nat) : Type :=
  | Unique : S.semty x -> result x
  | Ambig : S.semty x -> result x
  | Reject : nat -> result x.

  Definition finish (x x' : nat) (un : bool) (v' : S.semty x') : result x :=
    match Nat.eq_dec x' x with
    | left pf => let v := S.cast x' x pf v' in if un then Unique x v else Ambig x v
    | right _ => Reject x 1
    end.

  Definition measure (x : nat) (r : result x) : nat :=
    match r with Unique _ v => S.size x v | Ambig _ v => 100 + S.size x v | Reject _ n => 1000 + n end.
End Parser.

Module Syms <: SYMS.
  Definition semty (n : nat) : Type := match n with 0 => bool | S _ => nat end.
  Definition cast (a b : nat) (pf : a = b) (v : semty a) : semty b :=
    match pf in _ = b return semty b with eq_refl => v end.
  Definition default (n : nat) : semty n :=
    match n return semty n with 0 => true | S m => m end.
  Definition size (n : nat) : semty n -> nat :=
    match n return semty n -> nat with 0 => fun b => if b then 1 else 0 | S _ => fun v => v end.
End Syms.

Module P := Parser Syms.

Definition run : nat :=
  P.measure 3 (P.finish 3 3 true 7) + P.measure 3 (P.finish 3 3 false 7)
  + P.measure 3 (P.finish 3 4 true 7).

End ErasedLetNotResultType.

Crane Extraction "erased_let_not_result_type" ErasedLetNotResultType.
