From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
From Crane Require Extraction.

Module SuperfluousMoves.

Import IO_axioms.
Import MonadNotations.

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

(** A no-op effect used only to preserve the original monadic branch shape. *)
Axiom dummy : IO void.

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
Definition bad_branch (ls : loop_state) : IO (bool * loop_state) :=
  let gs1 := ls_game ls in
  let do_tick := true in
  let gs2 := if do_tick then tick gs1 else gs1 in
  match forced_mode with
  | Chase =>
    let gs3 := lose_one_life gs2 in
    if Nat.eqb (lives gs3) 0 then
      dummy ;;
      Ret (false, mkLoop gs3 (pacpos gs3) (ghosts gs3))
    else
      dummy ;;
      Ret (false, mkLoop gs3 (pacpos gs3) (ghosts gs3))
  | Frightened =>
    Ret (false, ls)
  end.

End SuperfluousMoves.

Import SuperfluousMoves.
Import IO_axioms.
Import MonadNotations.

(** Extracted C integer return type for a standalone entrypoint. *)
Axiom c_int : Type.

(** Zero exit code returned after forcing the reproduced branch. *)
Axiom c_zero : c_int.

(** Standalone entrypoint that forces evaluation of [bad_branch]. *)
Definition main : IO c_int :=
  res <- bad_branch sample_loop ;;
  let _ := snd res in
  Ret c_zero.

Crane Extract Inlined Constant dummy => "(void)0".
Crane Extract Inlined Constant c_int => "int".
Crane Extract Inlined Constant c_zero => "0".

Crane Extraction "superfluous_moves" SuperfluousMoves main.
