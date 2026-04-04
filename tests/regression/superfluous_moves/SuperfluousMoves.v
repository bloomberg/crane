From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Crane Require Extraction.

Module SuperfluousMoves.

(** Tiny position record so projections become shared-pointer field accesses. *)
Record position : Type := mkPos {
  px : nat
}.

(** Small mode enum to force a [switch] in the extracted C++. *)
Inductive mode : Type := Chase | Frightened.

(** Minimal source state carrying the projected fields that trigger the bug. *)
Record game_state : Type := mkState {
  pacpos : position;
  ghosts : list position;
  lives : nat
}.

(** Reduced loop state with only the three fields relevant to the bug. *)
Record loop_state : Type := mkLoop {
  ls_game : game_state;
  ls_prev_pac : position;
  ls_prev_ghosts : list position
}.

(** Identity tick so the reproducer stays minimal while keeping the same shape. *)
Definition tick (gs : game_state) : game_state := gs.

(** Life loss used to create the branch-local [gs3] value. *)
Definition lose_one_life (gs : game_state) : game_state :=
  mkState (mkPos 9) (ghosts gs) (Nat.pred (lives gs)).

(** Forces the same control-flow path as the original bug. *)
Definition forced_mode : mode := Chase.

(** Concrete state that makes the game-over branch fire after [lose_one_life]. *)
Definition sample_state : game_state :=
  mkState (mkPos 7) [mkPos 1; mkPos 2] 1.

(** Concrete loop state used by the standalone entrypoint. *)
Definition sample_loop : loop_state :=
  mkLoop sample_state (pacpos sample_state) (ghosts sample_state).

(** Reduced branch reproducer without the outer [option * nat] wrapper. *)
Definition bad_branch (ls : loop_state) : bool * loop_state :=
  let gs1 := ls_game ls in
  let do_tick := true in
  let gs2 := if do_tick then tick gs1 else gs1 in
  match forced_mode with
  | Chase =>
    let gs3 := lose_one_life gs2 in
    if Nat.eqb (lives gs3) 0 then
      (false, mkLoop gs3 (pacpos gs3) (ghosts gs3))
    else
      (false, mkLoop gs3 (pacpos gs3) (ghosts gs3))
  | Frightened =>
    (false, ls)
  end.

End SuperfluousMoves.

Crane Extraction "superfluous_moves" SuperfluousMoves.
