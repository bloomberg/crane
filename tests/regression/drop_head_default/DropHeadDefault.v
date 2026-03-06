(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: drop prefix and return head byte or default zero. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module DropHeadDefault.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | 0 => l
  | S n' =>
      match l with
      | [] => []
      | _ :: l' => drop n' l'
      end
  end.

Definition head_after_drop (rom : list nat) (addr : nat) : nat :=
  match drop addr rom with
  | b1 :: _ => b1
  | _ => 0
  end.

Definition t : nat := head_after_drop [5; 7; 9] 1.

End DropHeadDefault.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "drop_head_default" DropHeadDefault.
