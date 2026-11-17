(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A tail-recursive local fixpoint calling back into the function it is
    in, with loopification off.

    [scan] is in [find]'s flow and calls [find], so a machine of [find]
    could adopt it as a second entry; but no machine is made of a function
    Loopify does not loopify, and [scan] is a loop of its own.  Translation
    left every fixpoint some machine could adopt to Loopify, which lowered
    it when the unit was finished. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module LocalTailLoopCallsBack.

Inductive tree : Type := Leaf (n : nat) | Node (ts : list tree).

Fixpoint find (t : tree) (k : nat) {struct t} : option nat :=
  let fix scan (ts : list tree) (k : nat) {struct ts} : option nat :=
    match ts with
    | [] => None
    | t' :: ts' => if Nat.eqb k 0 then find t' k else scan ts' (k - 1)
    end in
  match t with
  | Leaf n => Some n
  | Node ts => scan ts k
  end.

End LocalTailLoopCallsBack.

Crane Extraction "local_tail_loop_calls_back" LocalTailLoopCallsBack.
