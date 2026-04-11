From Stdlib Require Import Bool.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.Std Monads.ITree.
From Crane Require Extraction.

Local Open Scope itree_scope.

Module CraneMoveHunt.

Record box : Type := mkBox {
  payload : nat;
  enabled : bool
}.

Record state : Type := mkState {
  core : box;
  cursor : box;
  visible : bool
}.

Definition clone_box (b : box) : box :=
  mkBox (payload b) (enabled b).

Definition keep_box (b : box) : box := b.

Definition use_box (b : box) : nat := payload b.

Definition use_state (s : state) : nat :=
  payload (core s) + payload (cursor s).

Definition render_state (s : state) : state :=
  mkState (core s) (cursor s) (visible s).

Definition sound_state (before after : state) : nat :=
  use_state before + use_state after.

Definition resolve_state (s : state) : state :=
  mkState (clone_box (core s)) (cursor s) (visible s).

Definition handle_state (s : state) : bool * state :=
  (visible s, render_state s).

Definition initial_box : box := mkBox 41 true.
Definition other_box : box := mkBox 1 false.
Definition initial_state : state := mkState initial_box other_box true.

Definition record_constant : box :=
  let b := keep_box initial_box in
  let b1 := clone_box b in
  let b2 := clone_box b in
  if enabled (keep_box b)
  then if enabled b then b2 else b1
  else b1.

Definition record_function (b0 : box) : box :=
  let b := keep_box b0 in
  let b1 := clone_box b in
  let b2 := clone_box b in
  if enabled (keep_box b)
  then if enabled b then b2 else b1
  else b1.

Definition state_constant : state :=
  let s1 := render_state initial_state in
  let _ := sound_state initial_state s1 in
  let _ := render_state s1 in
  let s2 := resolve_state s1 in
  let _ := sound_state s1 s2 in
  render_state s2.

Definition state_function (s0 : state) : state :=
  let s1 := render_state s0 in
  let _ := sound_state s0 s1 in
  let _ := render_state s1 in
  let s2 := resolve_state s1 in
  let _ := sound_state s1 s2 in
  render_state s2.

Definition match_reuse (s0 : state) : state :=
  let s1 := render_state s0 in
  if visible s1
  then
    let _ := sound_state s0 s1 in
    let s2 := resolve_state s1 in
    if visible s1 then s2 else s1
  else s1.

Definition boxed_payload (b : box) : nat := payload b.
Definition state_payload (s : state) : nat := payload (core s).

End CraneMoveHunt.

Import CraneMoveHunt.
Import ITreeNotations.

Inductive toyE : Type -> Type :=
| Tick : state -> toyE unit.

Crane Extract Skip toyE.

Definition tick (s : state) : itree toyE unit :=
  embed (Tick s).

Definition effect_frame (s0 : state) : itree toyE state :=
  let s1 := render_state s0 in
  tick s1 ;;
  tick s1 ;;
  let s2 := resolve_state s1 in
  tick s1 ;;
  tick s2 ;;
  Ret s2.

Definition effect_pair_frame (s0 : state) : itree toyE state :=
  let handled := handle_state s0 in
  let '(quit, s1) := handled in
  tick s1 ;;
  tick s1 ;;
  let s2 := resolve_state s1 in
  tick s1 ;;
  tick s2 ;;
  if quit then Ret s2 else Ret s1.

Definition pure_pair_frame (s0 : state) : state :=
  let handled := handle_state s0 in
  let '(quit, s1) := handled in
  let s2 := resolve_state s1 in
  let s3 := render_state s1 in
  if quit then s2 else s3.

Definition exported_record_constant : CraneMoveHunt.box :=
  CraneMoveHunt.record_constant.

Definition exported_record_function : CraneMoveHunt.box :=
  CraneMoveHunt.record_function CraneMoveHunt.initial_box.

Definition exported_state_constant : CraneMoveHunt.state :=
  CraneMoveHunt.state_constant.

Definition exported_state_function : CraneMoveHunt.state :=
  CraneMoveHunt.state_function CraneMoveHunt.initial_state.

Definition exported_match_reuse : CraneMoveHunt.state :=
  CraneMoveHunt.match_reuse CraneMoveHunt.initial_state.

Definition exported_effect_frame : itree toyE CraneMoveHunt.state :=
  effect_frame CraneMoveHunt.initial_state.

Definition exported_effect_pair_frame : itree toyE CraneMoveHunt.state :=
  effect_pair_frame CraneMoveHunt.initial_state.

Definition exported_pure_pair_frame : CraneMoveHunt.state :=
  CraneMoveHunt.pure_pair_frame CraneMoveHunt.initial_state.

Axiom tick_state : CraneMoveHunt.state -> unit.
Axiom tick_state_nat : CraneMoveHunt.state -> nat.

Definition axiom_pair_frame (s0 : CraneMoveHunt.state) : CraneMoveHunt.state :=
  let handled := CraneMoveHunt.handle_state s0 in
  let '(quit, s1) := handled in
  let _ := tick_state s1 in
  let _ := tick_state s1 in
  let s2 := CraneMoveHunt.resolve_state s1 in
  let _ := tick_state s1 in
  let _ := tick_state s2 in
  if quit then s2 else s1.

Definition exported_axiom_pair_frame : CraneMoveHunt.state :=
  axiom_pair_frame CraneMoveHunt.initial_state.

Definition axiom_nat_pair_frame (s0 : CraneMoveHunt.state) : CraneMoveHunt.state :=
  let handled := CraneMoveHunt.handle_state s0 in
  let '(quit, s1) := handled in
  let s2 := CraneMoveHunt.resolve_state s1 in
  let n := tick_state_nat s1 in
  if quit || Nat.eqb n 0 then s2 else s1.

Definition exported_axiom_nat_pair_frame : CraneMoveHunt.state :=
  axiom_nat_pair_frame CraneMoveHunt.initial_state.

Crane Extract Inlined Constant tick_state => "toy_tick(%a0)" From "toy_helpers.h".
Crane Extract Inlined Constant tick_state_nat => "toy_tick_nat(%a0)" From "toy_helpers.h".

Crane Extract Inductive toyE => ""
  [ "toy_tick(%a0)" ]
  From "toy_helpers.h".

Crane Extraction "crane_move_hunt"
  exported_record_constant
  exported_record_function
  exported_state_constant
  exported_state_function
  exported_match_reuse
  exported_effect_frame
  exported_effect_pair_frame
  exported_pure_pair_frame
  exported_axiom_pair_frame
  exported_axiom_nat_pair_frame.
