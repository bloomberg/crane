(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** [Set Crane Loopify]: an enum [switch] with a [default] branch ([| _ => ...])
    inside a tail-modulo-cons loop rewrites that branch as well, rather than
    leaving a raw [return] that exits the loop and drops the prefix built so
    far. *)
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LoopifyDefault.

Fixpoint merge_steps (n : nat) (xs ys : list nat) : list nat :=
  match n, xs, ys with
  | _, [], _ => ys
  | _, _, [] => xs
  | O, _, _ => xs
  | S n', x :: xs', y :: ys' =>
      match Nat.compare x y with
      | Gt => y :: merge_steps n' xs ys'
      | _ => x :: merge_steps n' xs' ys
      end
  end.

Fixpoint sum (l : list nat) : nat :=
  match l with [] => 0 | x :: r => x + sum r end.

Fixpoint len (l : list nat) : nat :=
  match l with [] => 0 | _ :: r => S (len r) end.

Definition merged : list nat := merge_steps 6 [1; 3; 5] [2; 4; 6].
Definition merged_len : nat := len merged.
Definition merged_sum : nat := sum merged.
Definition merged_head : nat := hd 99 merged.

End LoopifyDefault.

Set Crane Loopify.
Crane Extraction "loopify_default" LoopifyDefault.
