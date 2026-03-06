(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: recursive load_program over bytes. *)

From Stdlib Require Import List Nat.
Import ListNotations.

Module SequentialProgramLoad.

Record state : Type := MkState {
  rom_ : list nat;
  ptr' : nat
}.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Definition write_byte (s : state) (b : nat) : state :=
  MkState (update_nth (ptr' s) b (rom_ s)) (S (ptr' s)).

Fixpoint load_program (s : state) (bytes : list nat) : state :=
  match bytes with
  | [] => s
  | b :: rest => load_program (write_byte s b) rest
  end.

Definition sample : state := MkState [0; 0; 0; 0; 0] 1.
Definition t : nat := nth 2 (rom_ (load_program sample [5; 6; 7])) 0.

End SequentialProgramLoad.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "sequential_program_load" SequentialProgramLoad.
