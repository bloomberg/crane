(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: fetch 2-byte window with optional next pointer. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module FetchWindowNextPtr.

Fixpoint drop (n : nat) (l : list nat) : list nat :=
  match n with
  | 0 => l
  | S n' =>
      match l with
      | [] => []
      | _ :: l' => drop n' l'
      end
  end.

Definition fetch_window (rom : list nat) (addr : nat) : option (nat * nat) :=
  match drop addr rom with
  | b1 :: b2 :: _ => Some (b1, addr + 2)
  | _ => None
  end.

Definition t : nat :=
  match fetch_window [9; 8; 7] 0 with
  | Some (_, next) => next
  | None => 0
  end.

End FetchWindowNextPtr.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "fetch_window_next_ptr" FetchWindowNextPtr.
