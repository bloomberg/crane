(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: validated insulin workflow through mmol conversion, rounding, and pump delivery. *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Module ValidatedPumpDeliveryTraceCase.

Record Mg_dL : Type := mkBG { mg_dL_val : nat }.
Record Grams : Type := mkGrams { grams_val : nat }.

Definition Carbs_g := Grams.
Definition Minutes := nat.
Definition DIA_minutes := nat.
Definition Insulin_twentieth := nat.

Definition ONE_UNIT : nat := 20.
Definition BG_LEVEL2_HYPO : nat := 54.
Definition BG_HYPO : nat := 70.
Definition BG_HYPER : nat := 180.
Definition BG_METER_MIN : nat := 20.
Definition BG_METER_MAX : nat := 600.
Definition CARBS_SANITY_MAX : nat := 200.

Definition bg_in_meter_range (bg : Mg_dL) : bool :=
  (BG_METER_MIN <=? mg_dL_val bg) && (mg_dL_val bg <=? BG_METER_MAX).

Definition carbs_reasonable (carbs : Carbs_g) : bool :=
  grams_val carbs <=? CARBS_SANITY_MAX.

Record Config := mkConfig {
  cfg_bg_rise_per_gram : nat;
  cfg_conservative_cob_absorption_percent : nat;
  cfg_suspend_threshold_mg_dl : nat;
  cfg_stacking_warning_threshold_min : nat;
  cfg_iob_high_threshold_twentieths : nat
}.

Definition default_config : Config :=
  mkConfig 4 30 80 60 200.

Inductive ActivityState : Type :=
| Activity_Normal
| Activity_LightExercise
| Activity_ModerateExercise
| Activity_IntenseExercise
| Activity_Illness
| Activity_Stress.

Definition isf_activity_modifier (state : ActivityState) : nat :=
  match state with
  | Activity_Normal => 100
  | Activity_LightExercise => 110
  | Activity_ModerateExercise => 130
  | Activity_IntenseExercise => 150
  | Activity_Illness => 80
  | Activity_Stress => 90
  end.

Definition icr_activity_modifier (state : ActivityState) : nat :=
  match state with
  | Activity_Normal => 100
  | Activity_LightExercise => 110
  | Activity_ModerateExercise => 125
  | Activity_IntenseExercise => 140
  | Activity_Illness => 85
  | Activity_Stress => 95
  end.

Inductive FaultStatus : Type :=
| Fault_None
| Fault_Occlusion
| Fault_LowReservoir : nat -> FaultStatus
| Fault_BatteryLow
| Fault_Unknown.

Definition fault_blocks_bolus (f : FaultStatus) : bool :=
  match f with
  | Fault_None => false
  | Fault_Occlusion => true
  | Fault_LowReservoir remaining => remaining <? 10
  | Fault_BatteryLow => false
  | Fault_Unknown => true
  end.

Inductive InsulinType : Type :=
| Insulin_Humalog
| Insulin_Aspart
| Insulin_Lispro.

Definition peak_time (itype : InsulinType) (_ : DIA_minutes) : Minutes :=
  match itype with
  | Insulin_Humalog => 75
  | Insulin_Aspart => 70
  | Insulin_Lispro => 75
  end.

Record BolusEvent := mkBolusEvent {
  be_dose_twentieths : nat;
  be_time_minutes : Minutes
}.

Definition div_ceil (a b : nat) : nat :=
  if b =? 0 then 0 else (a + b - 1) / b.

Definition event_time_valid (now : Minutes) (event : BolusEvent) : bool :=
  be_time_minutes event <=? now.

Fixpoint history_times_valid (now : Minutes) (events : list BolusEvent) : bool :=
  match events with
  | [] => true
  | e :: rest => event_time_valid now e && history_times_valid now rest
  end.

Fixpoint history_sorted_from (prev : Minutes) (events : list BolusEvent) : bool :=
  match events with
  | [] => true
  | e :: rest =>
      (be_time_minutes e <=? prev) && history_sorted_from (be_time_minutes e) rest
  end.

Definition history_sorted_desc (events : list BolusEvent) : bool :=
  match events with
  | [] => true
  | e :: rest => history_sorted_from (be_time_minutes e) rest
  end.

Definition history_valid (now : Minutes) (events : list BolusEvent) : bool :=
  history_times_valid now events && history_sorted_desc events.

Definition bilinear_iob_fraction (elapsed : Minutes) (dia : DIA_minutes) (itype : InsulinType) : nat :=
  let pt := peak_time itype dia in
  if dia =? 0 then 0
  else if dia <=? elapsed then 0
  else if pt =? 0 then 0
  else if elapsed <=? pt then 100 - (elapsed * 25) / pt
  else if dia <=? pt then 0
  else ((dia - elapsed) * 75) / (dia - pt).

Definition bilinear_iob_from_bolus
  (now : Minutes)
  (event : BolusEvent)
  (dia : DIA_minutes)
  (itype : InsulinType)
  : Insulin_twentieth :=
  if now <? be_time_minutes event then 0
  else
    div_ceil
      (be_dose_twentieths event *
       bilinear_iob_fraction (now - be_time_minutes event) dia itype)
      100.

Fixpoint total_bilinear_iob
  (now : Minutes)
  (events : list BolusEvent)
  (dia : DIA_minutes)
  (itype : InsulinType)
  : Insulin_twentieth :=
  match events with
  | [] => 0
  | e :: rest => bilinear_iob_from_bolus now e dia itype + total_bilinear_iob now rest dia itype
  end.

Definition apply_sensor_margin (bg target : Mg_dL) : Mg_dL :=
  if mg_dL_val target <=? mg_dL_val bg
  then mkBG (mg_dL_val bg - (mg_dL_val bg * 15 / 100))
  else bg.

Definition adjusted_isf_tenths (bg : Mg_dL) (base_isf_tenths : nat) : nat :=
  if mg_dL_val bg <? 250 then base_isf_tenths
  else if mg_dL_val bg <? 350 then (base_isf_tenths * 80) / 100
  else (base_isf_tenths * 60) / 100.

Definition correction_twentieths_full
  (_ : Minutes)
  (current_bg target_bg : Mg_dL)
  (base_isf_tenths : nat)
  : Insulin_twentieth :=
  let eff_isf := adjusted_isf_tenths current_bg base_isf_tenths in
  if eff_isf =? 0 then 0
  else if mg_dL_val current_bg <=? mg_dL_val target_bg then 0
  else ((mg_dL_val current_bg - mg_dL_val target_bg) * 200) / eff_isf.

Definition apply_reverse_correction_twentieths
  (carb : Insulin_twentieth)
  (current_bg target_bg : Mg_dL)
  (isf_tenths : nat)
  : Insulin_twentieth :=
  if mg_dL_val current_bg <? mg_dL_val target_bg then
    let reverse_drop := mg_dL_val target_bg - mg_dL_val current_bg in
    let reverse_units :=
      if isf_tenths =? 0 then 0 else (reverse_drop * 200) / isf_tenths in
    if carb <=? reverse_units then 0 else carb - reverse_units
  else carb.

Inductive SuspendDecision : Type :=
| Suspend_None
| Suspend_Reduce : Insulin_twentieth -> SuspendDecision
| Suspend_Withhold.

Definition predict_bg_drop_tenths
  (iob_twentieths : Insulin_twentieth)
  (isf_tenths : nat)
  : nat :=
  if isf_tenths =? 0 then 0
  else (iob_twentieths * isf_tenths) / 200.

Definition conservative_cob_rise (cfg : Config) (cob_grams : nat) : nat :=
  (cob_grams * cfg_conservative_cob_absorption_percent cfg * cfg_bg_rise_per_gram cfg) / 100.

Definition predicted_eventual_bg_tenths
  (cfg : Config)
  (current_bg : Mg_dL)
  (iob_twentieths : Insulin_twentieth)
  (cob_grams : nat)
  (isf_tenths : nat)
  : nat :=
  let drop := predict_bg_drop_tenths iob_twentieths isf_tenths in
  let rise := conservative_cob_rise cfg cob_grams in
  let bg_after_drop :=
    if mg_dL_val current_bg <=? drop then 0 else mg_dL_val current_bg - drop in
  bg_after_drop + rise.

Definition suspend_check_tenths_with_cob
  (cfg : Config)
  (current_bg : Mg_dL)
  (iob_twentieths : Insulin_twentieth)
  (cob_grams : nat)
  (isf_tenths : nat)
  (proposed : Insulin_twentieth)
  : SuspendDecision :=
  if isf_tenths =? 0 then Suspend_Withhold
  else
    let total_insulin := iob_twentieths + proposed in
    let pred := predicted_eventual_bg_tenths cfg current_bg total_insulin cob_grams isf_tenths in
    if pred <? BG_LEVEL2_HYPO then Suspend_Withhold
    else if pred <? cfg_suspend_threshold_mg_dl cfg then
      let rise_from_cob := conservative_cob_rise cfg cob_grams in
      let effective_target :=
        if cfg_suspend_threshold_mg_dl cfg <=? rise_from_cob then 0
        else cfg_suspend_threshold_mg_dl cfg - rise_from_cob in
      let safe_drop :=
        if mg_dL_val current_bg <=? effective_target then 0
        else mg_dL_val current_bg - effective_target in
      let safe_insulin := (safe_drop * 200) / isf_tenths in
      if safe_insulin <=? iob_twentieths then Suspend_Withhold
      else Suspend_Reduce (safe_insulin - iob_twentieths)
    else Suspend_None.

Definition apply_suspend
  (proposed : Insulin_twentieth)
  (decision : SuspendDecision)
  : Insulin_twentieth :=
  match decision with
  | Suspend_None => proposed
  | Suspend_Reduce cap => if proposed <=? cap then proposed else cap
  | Suspend_Withhold => 0
  end.

Definition pediatric_max_twentieths (weight_kg : nat) : Insulin_twentieth :=
  weight_kg * 10.

Definition cap_pediatric (bolus : Insulin_twentieth) (weight_kg : nat) : Insulin_twentieth :=
  if bolus <=? pediatric_max_twentieths weight_kg then bolus else pediatric_max_twentieths weight_kg.

Record PrecisionParams := mkPrecisionParams {
  prec_icr_tenths : nat;
  prec_isf_tenths : nat;
  prec_target_bg : Mg_dL;
  prec_dia : DIA_minutes;
  prec_insulin_type : InsulinType
}.

Definition prec_params_valid (p : PrecisionParams) : bool :=
  (20 <=? prec_icr_tenths p) && (prec_icr_tenths p <=? 1000) &&
  (100 <=? prec_isf_tenths p) && (prec_isf_tenths p <=? 4000) &&
  (BG_HYPO <=? mg_dL_val (prec_target_bg p)) && (mg_dL_val (prec_target_bg p) <=? BG_HYPER) &&
  (120 <=? prec_dia p) && (prec_dia p <=? 360).

Record PrecisionInput := mkPrecisionInput {
  pi_carbs_g : Carbs_g;
  pi_current_bg : Mg_dL;
  pi_now : Minutes;
  pi_bolus_history : list BolusEvent;
  pi_activity : ActivityState;
  pi_use_sensor_margin : bool;
  pi_fault : FaultStatus;
  pi_weight_kg : option nat
}.

Definition carb_bolus_twentieths (carbs_g : nat) (icr_tenths : nat) : Insulin_twentieth :=
  if icr_tenths =? 0 then 0 else (carbs_g * 200) / icr_tenths.

Definition calculate_precision_bolus
  (input : PrecisionInput)
  (params : PrecisionParams)
  : Insulin_twentieth :=
  let activity_isf := (prec_isf_tenths params * isf_activity_modifier (pi_activity input)) / 100 in
  let activity_icr := (prec_icr_tenths params * icr_activity_modifier (pi_activity input)) / 100 in
  let eff_bg :=
    if pi_use_sensor_margin input
    then apply_sensor_margin (pi_current_bg input) (prec_target_bg params)
    else pi_current_bg input in
  let carb := carb_bolus_twentieths (grams_val (pi_carbs_g input)) activity_icr in
  let carb_adj := apply_reverse_correction_twentieths carb eff_bg (prec_target_bg params) activity_isf in
  let corr := correction_twentieths_full (pi_now input) eff_bg (prec_target_bg params) activity_isf in
  let iob :=
    total_bilinear_iob
      (pi_now input)
      (pi_bolus_history input)
      (prec_dia params)
      (prec_insulin_type params) in
  let raw := carb_adj + corr in
  if raw <=? iob then 0 else raw - iob.

Definition time_reasonable (now : Minutes) : bool :=
  now <=? 525600.

Definition history_extraction_safe (events : list BolusEvent) : bool :=
  (length events <=? 100) &&
  forallb (fun e => be_dose_twentieths e <=? 500) events.

Definition iob_high_threshold (cfg : Config) : nat :=
  cfg_iob_high_threshold_twentieths cfg.

Definition iob_dangerously_high (iob : Insulin_twentieth) : bool :=
  iob_high_threshold default_config <=? iob.

Inductive PrecisionResult : Type :=
| PrecOK : Insulin_twentieth -> bool -> PrecisionResult
| PrecError : nat -> PrecisionResult.

Definition prec_error_invalid_params : nat := 1.
Definition prec_error_invalid_input : nat := 2.
Definition prec_error_hypo : nat := 3.
Definition prec_error_invalid_history : nat := 4.
Definition prec_error_invalid_time : nat := 5.
Definition prec_error_stacking : nat := 6.
Definition prec_error_fault : nat := 7.
Definition prec_error_tdd_exceeded : nat := 8.
Definition prec_error_iob_high : nat := 9.
Definition prec_error_extraction_unsafe : nat := 10.

Definition bolus_too_soon (now : Minutes) (history : list BolusEvent) : bool :=
  match history with
  | [] => false
  | e :: _ =>
      if now <? be_time_minutes e then false
      else now - be_time_minutes e <? 15
  end.

Definition cap_twentieths (t : Insulin_twentieth) : Insulin_twentieth :=
  if t <=? 500 then t else 500.

Definition validated_precision_bolus
  (input : PrecisionInput)
  (params : PrecisionParams)
  : PrecisionResult :=
  if negb (prec_params_valid params) then PrecError prec_error_invalid_params
  else if negb (bg_in_meter_range (pi_current_bg input) && carbs_reasonable (pi_carbs_g input))
       then PrecError prec_error_invalid_input
  else if negb (time_reasonable (pi_now input))
       then PrecError prec_error_invalid_time
  else if negb (history_valid (pi_now input) (pi_bolus_history input))
       then PrecError prec_error_invalid_history
  else if negb (history_extraction_safe (pi_bolus_history input))
       then PrecError prec_error_extraction_unsafe
  else if bolus_too_soon (pi_now input) (pi_bolus_history input)
       then PrecError prec_error_stacking
  else if fault_blocks_bolus (pi_fault input)
       then PrecError prec_error_fault
  else if mg_dL_val (pi_current_bg input) <? BG_HYPO
       then PrecError prec_error_hypo
  else
    let iob :=
      total_bilinear_iob
        (pi_now input)
        (pi_bolus_history input)
        (prec_dia params)
        (prec_insulin_type params) in
    if iob_dangerously_high iob && (grams_val (pi_carbs_g input) =? 0)
    then PrecError prec_error_iob_high
    else
      let tdd_current :=
        fold_left
          (fun acc e =>
             if ((pi_now input) - 1440 <=? be_time_minutes e) && (be_time_minutes e <=? pi_now input)
             then acc + be_dose_twentieths e
             else acc)
          (pi_bolus_history input)
          0 in
      let tdd_limit :=
        match pi_weight_kg input with
        | None => 5000
        | Some w => w * ONE_UNIT
        end in
      if tdd_limit <=? tdd_current then PrecError prec_error_tdd_exceeded
      else
        let raw := calculate_precision_bolus input params in
        let tdd_capped :=
          if raw + tdd_current <=? tdd_limit then raw else tdd_limit - tdd_current in
        let activity_isf :=
          (prec_isf_tenths params * isf_activity_modifier (pi_activity input)) / 100 in
        let eff_bg :=
          if pi_use_sensor_margin input
          then apply_sensor_margin (pi_current_bg input) (prec_target_bg params)
          else pi_current_bg input in
        let suspend_decision :=
          suspend_check_tenths_with_cob
            default_config
            eff_bg
            iob
            (grams_val (pi_carbs_g input))
            activity_isf
            tdd_capped in
        let suspended := apply_suspend tdd_capped suspend_decision in
        let adult_capped := cap_twentieths suspended in
        let capped :=
          match pi_weight_kg input with
          | None => adult_capped
          | Some w => cap_pediatric adult_capped w
          end in
        let was_modified := negb (raw =? capped) in
        PrecOK capped was_modified.

Definition prec_result_twentieths (r : PrecisionResult) : option Insulin_twentieth :=
  match r with
  | PrecOK t _ => Some t
  | PrecError _ => None
  end.

Definition precision_result_code (r : PrecisionResult) : nat :=
  match r with
  | PrecOK _ _ => 0
  | PrecError code => code
  end.

Record MmolPrecisionInput := mkMmolPrecisionInput {
  mpi_carbs_g : Carbs_g;
  mpi_current_bg_mmol_tenths : nat;
  mpi_now : Minutes;
  mpi_bolus_history : list BolusEvent;
  mpi_activity : ActivityState;
  mpi_use_sensor_margin : bool;
  mpi_fault : FaultStatus;
  mpi_weight_kg : option nat
}.

Definition mmol_tenths_to_mg_dL (mmol_tenths : nat) : nat :=
  (mmol_tenths * 18) / 10.

Definition convert_mmol_input (input : MmolPrecisionInput) : PrecisionInput :=
  mkPrecisionInput
    (mpi_carbs_g input)
    (mkBG (mmol_tenths_to_mg_dL (mpi_current_bg_mmol_tenths input)))
    (mpi_now input)
    (mpi_bolus_history input)
    (mpi_activity input)
    (mpi_use_sensor_margin input)
    (mpi_fault input)
    (mpi_weight_kg input).

Definition validated_mmol_bolus
  (input : MmolPrecisionInput)
  (params : PrecisionParams)
  : PrecisionResult :=
  validated_precision_bolus (convert_mmol_input input) params.

Inductive RoundingMode : Type :=
| RoundTwentieth
| RoundTenth
| RoundHalf
| RoundUnit.

Definition round_down_to_increment (t increment : nat) : nat :=
  if increment =? 0 then t else (t / increment) * increment.

Definition apply_rounding (mode : RoundingMode) (t : Insulin_twentieth) : Insulin_twentieth :=
  match mode with
  | RoundTwentieth => t
  | RoundTenth => round_down_to_increment t 2
  | RoundHalf => round_down_to_increment t 10
  | RoundUnit => round_down_to_increment t ONE_UNIT
  end.

Definition final_delivery
  (mode : RoundingMode)
  (result : PrecisionResult)
  : option Insulin_twentieth :=
  match result with
  | PrecOK t _ => Some (apply_rounding mode t)
  | PrecError _ => None
  end.

Record PumpState := mkPumpState {
  ps_reservoir_twentieths : nat;
  ps_basal_rate_hundredths : nat;
  ps_last_bolus_time : Minutes;
  ps_occlusion_detected : bool;
  ps_battery_percent : nat
}.

Definition pump_can_deliver (state : PumpState) (dose : Insulin_twentieth) : bool :=
  negb (ps_occlusion_detected state) &&
  (dose <=? ps_reservoir_twentieths state) &&
  (dose <=? 500) &&
  (5 <=? ps_battery_percent state).

Definition reservoir_after_bolus (state : PumpState) (dose : Insulin_twentieth) : nat :=
  if dose <=? ps_reservoir_twentieths state
  then ps_reservoir_twentieths state - dose
  else 0.

Definition option_nat_default (x : option nat) (d : nat) : nat :=
  match x with
  | Some v => v
  | None => d
  end.

Definition result_modified (r : PrecisionResult) : bool :=
  match r with
  | PrecOK _ changed => changed
  | PrecError _ => false
  end.

Definition pump_accepts_result (pump : PumpState) (mode : RoundingMode) (r : PrecisionResult) : bool :=
  match final_delivery mode r with
  | Some dose => pump_can_deliver pump dose
  | None => false
  end.

Definition pump_reservoir_after_result (pump : PumpState) (mode : RoundingMode) (r : PrecisionResult) : nat :=
  match final_delivery mode r with
  | Some dose => reservoir_after_bolus pump dose
  | None => ps_reservoir_twentieths pump
  end.

Definition witness_prec_params : PrecisionParams :=
  mkPrecisionParams 100 500 (mkBG 100) 240 Insulin_Humalog.

Definition standard_input : PrecisionInput :=
  mkPrecisionInput (mkGrams 60) (mkBG 150) 0 [] Activity_Normal false Fault_None None.

Definition mmol_input : MmolPrecisionInput :=
  mkMmolPrecisionInput (mkGrams 60) 83 0 [] Activity_Normal false Fault_None None.

Definition high_iob_input : PrecisionInput :=
  mkPrecisionInput (mkGrams 0) (mkBG 150) 100
    [mkBolusEvent 120 85; mkBolusEvent 100 80]
    Activity_Normal false Fault_None None.

Definition tdd_exceeded_input : PrecisionInput :=
  mkPrecisionInput (mkGrams 60) (mkBG 150) 2000
    [mkBolusEvent 500 1800; mkBolusEvent 500 1500; mkBolusEvent 500 1000]
    Activity_Normal false Fault_None (Some 70).

Definition occlusion_input : PrecisionInput :=
  mkPrecisionInput (mkGrams 60) (mkBG 150) 120
    [mkBolusEvent 40 100]
    Activity_Normal false Fault_Occlusion None.

Definition battery_low_input : PrecisionInput :=
  mkPrecisionInput (mkGrams 60) (mkBG 150) 120
    [mkBolusEvent 40 100]
    Activity_Normal false Fault_BatteryLow None.

Definition pediatric_capped_input : PrecisionInput :=
  mkPrecisionInput (mkGrams 200) (mkBG 400) 0 [] Activity_Normal false Fault_None (Some 20).

Definition standard_pump : PumpState :=
  mkPumpState 2000 100 0 false 80.

Definition low_battery_pump : PumpState :=
  mkPumpState 2000 100 0 false 4.

Definition standard_result : PrecisionResult :=
  validated_precision_bolus standard_input witness_prec_params.

Definition mmol_result : PrecisionResult :=
  validated_mmol_bolus mmol_input witness_prec_params.

Definition battery_low_result : PrecisionResult :=
  validated_precision_bolus battery_low_input witness_prec_params.

Definition pediatric_result : PrecisionResult :=
  validated_precision_bolus pediatric_capped_input witness_prec_params.

Definition standard_result_code : nat :=
  precision_result_code standard_result.

Definition standard_modified : bool :=
  result_modified standard_result.

Definition standard_final_delivery_half : nat :=
  option_nat_default (final_delivery RoundHalf standard_result) 0.

Definition standard_pump_accepts : bool :=
  pump_accepts_result standard_pump RoundHalf standard_result.

Definition standard_reservoir_after : nat :=
  pump_reservoir_after_result standard_pump RoundHalf standard_result.

Definition mmol_result_code : nat :=
  precision_result_code mmol_result.

Definition mmol_final_delivery_tenth : nat :=
  option_nat_default (final_delivery RoundTenth mmol_result) 0.

Definition high_iob_error_code : nat :=
  precision_result_code (validated_precision_bolus high_iob_input witness_prec_params).

Definition tdd_error_code : nat :=
  precision_result_code (validated_precision_bolus tdd_exceeded_input witness_prec_params).

Definition occlusion_error_code : nat :=
  precision_result_code (validated_precision_bolus occlusion_input witness_prec_params).

Definition battery_low_result_code : nat :=
  precision_result_code battery_low_result.

Definition battery_low_pump_denied : bool :=
  negb (pump_accepts_result low_battery_pump RoundHalf battery_low_result).

Definition pediatric_result_code : nat :=
  precision_result_code pediatric_result.

Definition pediatric_modified : bool :=
  result_modified pediatric_result.

Definition pediatric_final_delivery : nat :=
  option_nat_default (final_delivery RoundTwentieth pediatric_result) 0.

Definition low_reservoir_blocks : bool :=
  fault_blocks_bolus (Fault_LowReservoir 5).

Definition unknown_fault_blocks : bool :=
  fault_blocks_bolus Fault_Unknown.

End ValidatedPumpDeliveryTraceCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "validated_pump_delivery_trace" ValidatedPumpDeliveryTraceCase.
