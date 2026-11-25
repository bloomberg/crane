(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A recursive function generic over an event family [E'], taking an ST
    array whose phantom state [S] the C++ type does not mention.  Its
    self-call writes no value for [S]: the template head writes [S]'s filler
    ([void]) only so that it can write [E'] after it.  The filler was read as
    the call's instantiation of [S], so the array argument was checked
    against [STArray nat void nat] and the typed-fit check failed. *)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lia List.
From ITree Require Import ITree Events.Exception.
From Crane Require Import Mapping.NatIntStd Monads.ITree Monads.Error
  Monads.Indices Monads.STMonad.
Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Module PhantomFillerNotWritten.
Section Scan.
  Context {S : Type}.
  Let V : nat -> Type := fun _ => nat.

  (** The sum of [arr[i..hi-1]], by recursion on the accessibility of
      [hi - i]. *)
  Fixpoint sum_from {E' : Type -> Type} `{STEvent nat S V -< E'}
    (arr : STArray nat S nat) (hi i : nat) (acc : Acc lt (hi - i)) {struct acc}
    : itree E' nat :=
    match Sumbool.sumbool_of_bool (Nat.ltb i hi) with
    | left Hlt =>
      v <- readArray (E := E') (V := V) (idx := 0) arr i;;
      r <- @sum_from E' _ arr hi (Datatypes.S i)
             (@Acc_inv _ _ _ acc (hi - Datatypes.S i)
                ltac:(apply Nat.ltb_lt in Hlt; lia));;
      Ret (v + r)
    | right _ => Ret 0
    end.

End Scan.

Definition sum_list (xs : list nat)
  : itree (STEvent nat unit (fun _ => nat) +' exceptE Err) nat :=
  arr <- newListArray 0 0 (length xs - 1) xs;;
  sum_from arr (length xs) 0 (lt_wf _).

End PhantomFillerNotWritten.

Crane Extraction "phantom_filler_not_written" PhantomFillerNotWritten.
