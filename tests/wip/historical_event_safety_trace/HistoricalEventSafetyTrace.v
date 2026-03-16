(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: historical event harness, proof-carrying plant/rating bundles, and Hoover-style scenario tracing. *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Module HistoricalEventSafetyTraceCase.

Record State : Type := mkState {
  reservoir_level_cm : nat;
  downstream_stage_cm : nat;
  gate_open_pct : nat
}.

Record PlantConfig : Type := mkPlantConfig {
  max_reservoir_cm : nat;
  max_downstream_cm : nat;
  gate_capacity_cm : nat;
  forecast_error_pct : nat;
  gate_slew_pct : nat;
  max_stage_rise_cm : nat;
  reservoir_area_min_cm2 : nat;
  reservoir_area_max_cm2 : nat;
  reservoir_area_curve_cm2 : nat -> nat;
  design_head_cm : nat;
  timestep_s : nat;
  pc_max_reservoir_pos : max_reservoir_cm > 0;
  pc_max_downstream_pos : max_downstream_cm > 0;
  pc_gate_capacity_pos : gate_capacity_cm > 0;
  pc_reservoir_area_min_pos : reservoir_area_min_cm2 > 0;
  pc_reservoir_area_curve_bounds :
    forall h, reservoir_area_min_cm2 <= reservoir_area_curve_cm2 h <= reservoir_area_max_cm2;
  pc_design_head_pos : design_head_cm > 0;
  pc_timestep_pos : timestep_s > 0
}.

Definition is_safe_bool (pconf : PlantConfig) (s : State) : bool :=
  Nat.leb (reservoir_level_cm s) (max_reservoir_cm pconf) &&
  Nat.leb (downstream_stage_cm s) (max_downstream_cm pconf).

Record InflowRecord : Type := mkInflowRecord {
  ir_timestep : nat;
  ir_inflow_cm : nat
}.

Definition HistoricalEvent := list InflowRecord.

Fixpoint event_to_inflow (event : HistoricalEvent) (default_inflow : nat) (t : nat) : nat :=
  match event with
  | nil => default_inflow
  | rec :: rest =>
      if Nat.eqb t (ir_timestep rec)
      then ir_inflow_cm rec
      else event_to_inflow rest default_inflow t
  end.

Record TestResult : Type := mkTestResult {
  tr_event_name : nat;
  tr_initial_safe : bool;
  tr_final_safe : bool;
  tr_max_level : nat;
  tr_max_stage : nat
}.

Definition step_hist
  (inflow : nat -> nat)
  (ctrl : State -> nat -> nat)
  (stage_fn : nat -> nat)
  (pconf : PlantConfig)
  (s : State)
  (t : nat)
  : State :=
  let out := Nat.min (gate_capacity_cm pconf * ctrl s t / 100)
                     (reservoir_level_cm s + inflow t) in
  let new_level := reservoir_level_cm s + inflow t - out in
  let new_stage := stage_fn out in
  {| reservoir_level_cm := new_level;
     downstream_stage_cm := new_stage;
     gate_open_pct := ctrl s t |}.

Fixpoint simulate_with_max
  (inflow : nat -> nat)
  (ctrl : State -> nat -> nat)
  (stage_fn : nat -> nat)
  (pconf : PlantConfig)
  (horizon : nat)
  (s : State)
  (max_level max_stage : nat)
  : State * nat * nat :=
  match horizon with
  | O => (s, max_level, max_stage)
  | S k =>
      let s' := step_hist inflow ctrl stage_fn pconf s k in
      simulate_with_max inflow ctrl stage_fn pconf k s'
        (Nat.max max_level (reservoir_level_cm s'))
        (Nat.max max_stage (downstream_stage_cm s'))
  end.

Definition run_historical_test
  (pconf : PlantConfig)
  (event : HistoricalEvent)
  (default_inflow : nat)
  (ctrl : State -> nat -> nat)
  (stage_fn : nat -> nat)
  (initial_state : State)
  (horizon : nat)
  (event_id : nat)
  : TestResult :=
  let inflow := event_to_inflow event default_inflow in
  let initial_safe := is_safe_bool pconf initial_state in
  let '(final_state, max_lev, max_stg) :=
      simulate_with_max inflow ctrl stage_fn pconf horizon initial_state 0 0 in
  let final_safe := is_safe_bool pconf final_state in
  {| tr_event_name := event_id;
     tr_initial_safe := initial_safe;
     tr_final_safe := final_safe;
     tr_max_level := max_lev;
     tr_max_stage := max_stg |}.

Definition test_passes (result : TestResult) : bool :=
  tr_initial_safe result && tr_final_safe result.

Fixpoint all_tests_pass (results : list TestResult) : bool :=
  match results with
  | nil => true
  | r :: rest => test_passes r && all_tests_pass rest
  end.

Definition RatingTable := list (nat * nat).

Fixpoint stage_from_table (tbl : RatingTable) (base_stage : nat) (out : nat) : nat :=
  match tbl with
  | [] => base_stage
  | (q, s) :: rest =>
      let tail := stage_from_table rest base_stage out in
      if Nat.leb out q then s else Nat.max s tail
  end.

Fixpoint monotone_table (tbl : RatingTable) : Prop :=
  match tbl with
  | [] => True
  | _ :: [] => True
  | (q1, s1) :: rest =>
      match rest with
      | [] => True
      | (q2, s2) :: _ => q1 <= q2 /\ s1 <= s2 /\ monotone_table rest
      end
  end.

Record MonotoneRatingTable : Type := mkMonotoneTable {
  mrt_table : RatingTable;
  mrt_monotone : monotone_table mrt_table
}.

Arguments mrt_table _.

Definition flood_1983_inflows : HistoricalEvent :=
  [ mkInflowRecord 0 50;
    mkInflowRecord 1 75;
    mkInflowRecord 2 100;
    mkInflowRecord 3 150;
    mkInflowRecord 4 200;
    mkInflowRecord 5 250;
    mkInflowRecord 6 300;
    mkInflowRecord 7 250;
    mkInflowRecord 8 200;
    mkInflowRecord 9 150 ].

Definition flood_2011_inflows : HistoricalEvent :=
  [ mkInflowRecord 0 100;
    mkInflowRecord 1 150;
    mkInflowRecord 2 200;
    mkInflowRecord 3 300;
    mkInflowRecord 4 400;
    mkInflowRecord 5 350;
    mkInflowRecord 6 300;
    mkInflowRecord 7 250;
    mkInflowRecord 8 200;
    mkInflowRecord 9 150 ].

Definition dual_peak_scenario : HistoricalEvent :=
  [ mkInflowRecord 0 30;
    mkInflowRecord 1 60;
    mkInflowRecord 2 120;
    mkInflowRecord 3 200;
    mkInflowRecord 4 300;
    mkInflowRecord 5 380;
    mkInflowRecord 6 420;
    mkInflowRecord 7 400;
    mkInflowRecord 8 350;
    mkInflowRecord 9 280 ].

Definition hist_witness_plant : PlantConfig.
Proof.
  refine (@mkPlantConfig
    500 500 500 1 5 10 100 100
    (fun _ => 100)
    100 1
    _ _ _ _ _ _ _).
  all: abstract (intros; lia).
Defined.

Definition hist_witness_stage (out : nat) : nat := out / 2.

Definition hist_witness_ctrl (s : State) (_ : nat) : nat :=
  if Nat.leb 90 (reservoir_level_cm s) then 100 else 50.

Definition hist_witness_initial : State :=
  {| reservoir_level_cm := 50;
     downstream_stage_cm := 0;
     gate_open_pct := 0 |}.

Definition hist_test_1983 : TestResult :=
  run_historical_test
    hist_witness_plant
    flood_1983_inflows
    0
    hist_witness_ctrl
    hist_witness_stage
    hist_witness_initial
    10
    1983.

Definition hist_test_2011 : TestResult :=
  run_historical_test
    hist_witness_plant
    flood_2011_inflows
    0
    hist_witness_ctrl
    hist_witness_stage
    hist_witness_initial
    10
    2011.

Definition hoover_dam_config : PlantConfig.
Proof.
  refine (@mkPlantConfig
    2200 100 500 15 5 10 1000 1000
    (fun _ => 1000)
    200 60
    _ _ _ _ _ _ _).
  all: abstract (intros; lia).
Defined.

Definition hoover_initial_state : State :=
  {| reservoir_level_cm := 1500;
     downstream_stage_cm := 20;
     gate_open_pct := 0 |}.

Definition hoover_controller (s : State) (_ : nat) : nat :=
  if Nat.leb 2000 (reservoir_level_cm s) then 100
  else if Nat.leb 1900 (reservoir_level_cm s) then 75
  else if Nat.leb 1800 (reservoir_level_cm s) then 50
  else if Nat.leb 1700 (reservoir_level_cm s) then 25
  else 0.

Definition hoover_rating_table : MonotoneRatingTable.
Proof.
  refine (mkMonotoneTable [(100, 30); (200, 45); (300, 60); (400, 75); (500, 90)] _).
  vm_compute. repeat split; lia.
Defined.

Definition hoover_stage_from_rating (out : nat) : nat :=
  stage_from_table (mrt_table hoover_rating_table) 20 out.

Definition hoover_test : TestResult :=
  run_historical_test
    hoover_dam_config
    dual_peak_scenario
    0
    hoover_controller
    hoover_stage_from_rating
    hoover_initial_state
    10
    9001.

Record HistoricalScenarioBundle : Type := mkHistoricalScenarioBundle {
  hsb_hist_plant : PlantConfig;
  hsb_hist_table : MonotoneRatingTable;
  hsb_hist_initial : State;
  hsb_test_1983 : TestResult;
  hsb_test_2011 : TestResult;
  hsb_hoover_plant : PlantConfig;
  hsb_hoover_test : TestResult
}.

Definition historical_bundle : HistoricalScenarioBundle :=
  mkHistoricalScenarioBundle
    hist_witness_plant
    hoover_rating_table
    hist_witness_initial
    hist_test_1983
    hist_test_2011
    hoover_dam_config
    hoover_test.

Definition historical_lookup_1983 (t : nat) : nat :=
  event_to_inflow flood_1983_inflows 0 t.

Definition historical_lookup_2011 (t : nat) : nat :=
  event_to_inflow flood_2011_inflows 0 t.

Definition witness_test_initial_safe_at (h : nat) : bool :=
  tr_initial_safe
    (run_historical_test
      hist_witness_plant
      flood_1983_inflows
      0
      hist_witness_ctrl
      hist_witness_stage
      hist_witness_initial
      h
      1983).

Definition witness_test_peak_level_at (h : nat) : nat :=
  tr_max_level
    (run_historical_test
      hist_witness_plant
      flood_2011_inflows
      0
      hist_witness_ctrl
      hist_witness_stage
      hist_witness_initial
      h
      2011).

Definition hoover_controller_sample (level : nat) : nat :=
  hoover_controller
    {| reservoir_level_cm := level;
       downstream_stage_cm := 20;
       gate_open_pct := 0 |}
    0.

Definition hoover_stage_sample (out : nat) : nat :=
  hoover_stage_from_rating out.

Definition sample_bundle_test_count : nat :=
  length [hsb_test_1983 historical_bundle; hsb_test_2011 historical_bundle; hsb_hoover_test historical_bundle].

Definition sample_bundle_initial_safe : bool :=
  tr_initial_safe (hsb_test_1983 historical_bundle).

Definition sample_bundle_hist_2011_id : nat :=
  tr_event_name (hsb_test_2011 historical_bundle).

Definition sample_all_tests_pass : bool :=
  all_tests_pass
    [hsb_test_1983 historical_bundle;
     hsb_test_2011 historical_bundle;
     hsb_hoover_test historical_bundle].

End HistoricalEventSafetyTraceCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "historical_event_safety_trace" HistoricalEventSafetyTraceCase.
