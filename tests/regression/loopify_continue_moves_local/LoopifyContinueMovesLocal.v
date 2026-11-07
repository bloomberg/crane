From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Set Crane Loopify.

(** A tail loop moves a local of its turn into a parameter's next value
    where the turn owns it and reads it there for the last time
    (Ownership_ir.continue_moves, Move_argument): where nothing reads it
    after but the Continue's other arguments, by name, it is moved at the
    last of the loop's updates that reads it.  A part of it read by another
    argument keeps it copied. *)
Module LoopifyContinueMovesLocal.

Fixpoint count_down (n : nat) (acc : list nat) : list nat :=
  match n with
  | O => acc
  | S m =>
    let next := m :: acc in
    count_down m next
  end.

(** [next] is read by the count as well, which is updated first. *)
Fixpoint count_both (n : nat) (acc : list nat) (k : nat) : list nat * nat :=
  match n with
  | O => (acc, k)
  | S m =>
    let next := m :: acc in
    count_both m next (k + length next)
  end.

(** The local is passed to one parameter, its tail, computed by a call
    on it, to another. *)
Fixpoint split_off (n : nat) (acc : list nat) (rest : list nat) : list nat * list nat :=
  match n with
  | O => (acc, rest)
  | S m =>
    let next := m :: acc in
    split_off m next (tl next)
  end.

(** The local is passed to one parameter, the tail its match binds to
    another: a part of it, read by name only there, so it is copied. *)
Fixpoint peel (n : nat) (acc : list nat) (rest : list nat) : list nat * list nat :=
  match n with
  | O => (acc, rest)
  | S m =>
    let next := m :: acc in
    match next with
    | [] => (acc, rest)
    | _ :: t => peel m next t
    end
  end.

Definition test_count_down : list nat := count_down 3 [].
Definition test_count_both : list nat * nat := count_both 3 [] 0.
Definition test_split_off : list nat * list nat := split_off 3 [] [].
Definition test_peel : list nat * list nat := peel 3 [] [].

End LoopifyContinueMovesLocal.

Crane Extraction "loopify_continue_moves_local" LoopifyContinueMovesLocal.
