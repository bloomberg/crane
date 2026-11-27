From Crane Require Import Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.

(** A memoised longest-prefix scan shaped like ParseALot's [max_pref_fn_M],
    over a list mapped to a cons list whose match template binds the tail as
    a variable of its own ([auto %b1a1 = %scrut.tail()]) and the head by
    reference.  The tail is a copy, not a part of the scrutinee: the call
    entering the machine takes it by move.  The frame saved across the call
    copies the head, a part of the list, before moving the list in after it,
    instead of copying the list. *)
Module FrameSaveCopiedBinder.

Definition accepting (st : list nat) : bool :=
  match st with
  | x :: _ => even x
  | [] => false
  end.

Definition step (a : nat) (st : list nat) : list nat := a :: st.

Definition lookup (m : option nat) (a : nat) : option (option (list nat * list nat * nat)) :=
  match m with
  | Some k => if k =? a then Some None else None
  | None => None
  end.

Fixpoint scan (m : option nat) (s : list nat) (i : nat) (st : list nat)
  : nat * option (list nat * list nat * nat) :=
  match s with
  | [] => if accepting st then (0, Some ([], [], i)) else (1, None)
  | a :: s' =>
    let st' := step a st in
    let mp :=
      match lookup m a with
      | None => scan m s' (pred i) st'
      | Some o => (2, o)
      end
    in
    match mp with
    | (c, None) =>
      if accepting st' then (c, Some ([a], s', pred i))
      else if accepting st then (c, Some ([], s, i))
      else (S c, None)
    | (c, Some (p, q, qi)) => (c, Some (a :: p, q, qi))
    end
  end.

End FrameSaveCopiedBinder.

Crane Extract Inductive list =>
  "crane::list<%t0>"
  [ "crane::list<%t0>{}"
    "crane::cons(%a0, %a1)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.tail(); %br1 }"
  From "conslist.h".

Set Crane Loopify.
Crane Extraction "frame_save_copied_binder" FrameSaveCopiedBinder.
