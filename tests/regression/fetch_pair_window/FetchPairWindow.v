(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: fetch two-byte window with pair fallback defaults. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module FetchPairWindow.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | 0 => l
  | S n' =>
      match l with
      | [] => []
      | _ :: l' => drop n' l'
      end
  end.

Definition fetch_pair (rom : list nat) (addr : nat) : nat * nat :=
  match drop addr rom with
  | b1 :: b2 :: _ => (b1, b2)
  | _ => (0, 0)
  end.

Definition t : nat :=
  let p := fetch_pair [1; 2; 3] 0 in
  fst p + snd p.

End FetchPairWindow.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "fetch_pair_window" FetchPairWindow.
