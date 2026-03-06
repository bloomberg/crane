(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: guarded ROM write on PROM-enable state. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module GuardedPromWrite.

Record state : Type := MkState {
  rom_ : list nat;
  prom_addr_ : nat;
  prom_data_ : nat;
  prom_enable_ : bool
}.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Definition execute_wpm (s : state) : state :=
  if prom_enable_ s
  then MkState (update_nth (prom_addr_ s) (prom_data_ s) (rom_ s))
               (prom_addr_ s) (prom_data_ s) (prom_enable_ s)
  else s.

Definition sample : state := MkState [0; 0; 0] 1 9 true.
Definition t : nat := nth 1 (rom_ (execute_wpm sample)) 0.

End GuardedPromWrite.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "guarded_prom_write" GuardedPromWrite.
