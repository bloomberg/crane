(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [count] is declared
      [template <typename T1 = void, template <typename> class T2>]
    ([T1] the phantom state [S], [T2] the family [F]), and the call in
    [count_list] writes [count<void>(...)]: [F := list] is not written, and
    C++ cannot deduce it ("couldn't infer template argument 'T2'"). *)

From Stdlib Require Import List.
From ITree Require Import ITree Events.Exception.
From Crane Require Import Mapping.NatIntStd Monads.ITree Monads.Error
  Monads.Indices Monads.STMonad.
Import Monads.
Local Open Scope monad_scope.

Module HkArgumentAfterPhantom.
Section Count.
  Context {S : Type}.

  Fixpoint count {F : Type -> Type} (arr : STArray nat S nat) (n : nat) : option (F nat) :=
    match n with
    | Datatypes.S n0 => count (F := F) arr n0
    | O => None
    end.
End Count.

Definition count_list (xs : list nat)
  : itree (STEvent nat unit (fun _ => nat) +' exceptE Err) bool :=
  arr <- newListArray 0 0 (length xs - 1) xs;;
  Ret (match count (F := list) arr (length xs) with None => true | Some _ => false end).
End HkArgumentAfterPhantom.

Crane Extraction "hk_argument_after_phantom" HkArgumentAfterPhantom.
