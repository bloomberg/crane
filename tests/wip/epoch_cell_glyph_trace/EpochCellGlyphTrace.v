(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: epoch cell and glyph tracing over mechanism state and eclipse records. *)

From Stdlib Require Import List Bool ZArith QArith.
Import ListNotations.
Open Scope Z_scope.

Module EpochCellGlyphTraceCase.

Inductive LunarPhase : Set :=
| NewMoon
| FirstQuarter
| FullMoon
| LastQuarter.

Definition phase_code (p : LunarPhase) : nat :=
  match p with
  | NewMoon => 0
  | FirstQuarter => 1
  | FullMoon => 2
  | LastQuarter => 3
  end.

Definition phase_from_angle (angle_deg : Z) : LunarPhase :=
  let wrapped := (angle_deg mod 360)%Z in
  if (wrapped <? 45)%Z then NewMoon
  else if (wrapped <? 135)%Z then FirstQuarter
  else if (wrapped <? 225)%Z then FullMoon
  else if (wrapped <? 315)%Z then LastQuarter
  else NewMoon.

Inductive ZodiacSign : Set :=
| Aries
| Taurus
| Gemini
| Cancer
| Leo
| Virgo
| Libra
| Scorpio
| Sagittarius
| Capricorn
| Aquarius
| Pisces.

Definition zodiac_code (z : ZodiacSign) : nat :=
  match z with
  | Aries => 0
  | Taurus => 1
  | Gemini => 2
  | Cancer => 3
  | Leo => 4
  | Virgo => 5
  | Libra => 6
  | Scorpio => 7
  | Sagittarius => 8
  | Capricorn => 9
  | Aquarius => 10
  | Pisces => 11
  end.

Definition eclipse_possible_at_dial (dial_pos : Z) : bool :=
  if (dial_pos =? 1)%Z then true
  else if (dial_pos =? 6)%Z then true
  else if (dial_pos =? 12)%Z then true
  else if (dial_pos =? 17)%Z then true
  else false.

Record MechanismState := mkState {
  crank_position : Z;
  metonic_dial : Z;
  saros_dial : Z;
  callippic_dial : Z;
  exeligmos_dial : Z;
  games_dial : Z;
  zodiac_position : Z
}.

Definition initial_state : MechanismState := mkState 0 0 0 0 0 0 0.

Definition metonic_modulus : Z := 235.
Definition saros_modulus : Z := 223.
Definition callippic_modulus : Z := 76.
Definition exeligmos_modulus : Z := 3.
Definition games_modulus : Z := 4.
Definition zodiac_modulus : Z := 360.

Definition step (s : MechanismState) : MechanismState :=
  mkState
    (crank_position s + 1)
    ((metonic_dial s + 1) mod metonic_modulus)
    ((saros_dial s + 1) mod saros_modulus)
    ((callippic_dial s + 1) mod callippic_modulus)
    ((exeligmos_dial s + 1) mod exeligmos_modulus)
    ((games_dial s + 1) mod games_modulus)
    ((zodiac_position s + 1) mod zodiac_modulus).

Definition step_reverse (s : MechanismState) : MechanismState :=
  mkState
    (crank_position s - 1)
    ((metonic_dial s - 1 + metonic_modulus) mod metonic_modulus)
    ((saros_dial s - 1 + saros_modulus) mod saros_modulus)
    ((callippic_dial s - 1 + callippic_modulus) mod callippic_modulus)
    ((exeligmos_dial s - 1 + exeligmos_modulus) mod exeligmos_modulus)
    ((games_dial s - 1 + games_modulus) mod games_modulus)
    ((zodiac_position s - 1 + zodiac_modulus) mod zodiac_modulus).

Fixpoint step_n (n : nat) (s : MechanismState) : MechanismState :=
  match n with
  | O => s
  | S rest => step_n rest (step s)
  end.

Definition state_at_cell (cell : Z) : MechanismState :=
  mkState cell cell cell cell cell cell cell.

Definition predict_moon_phase_from_state (s : MechanismState) : LunarPhase :=
  let phase_angle := (metonic_dial s * 360 / 235)%Z in
  phase_from_angle phase_angle.

Definition predict_olympiad_year (s : MechanismState) : Z :=
  ((games_dial s mod 4) + 1)%Z.

Definition predict_zodiac_sign (s : MechanismState) : ZodiacSign :=
  let deg := (zodiac_position s mod 360)%Z in
  if (deg <? 30)%Z then Aries
  else if (deg <? 60)%Z then Taurus
  else if (deg <? 90)%Z then Gemini
  else if (deg <? 120)%Z then Cancer
  else if (deg <? 150)%Z then Leo
  else if (deg <? 180)%Z then Virgo
  else if (deg <? 210)%Z then Libra
  else if (deg <? 240)%Z then Scorpio
  else if (deg <? 270)%Z then Sagittarius
  else if (deg <? 300)%Z then Capricorn
  else if (deg <? 330)%Z then Aquarius
  else Pisces.

Inductive EclipseCategory : Set :=
| EC_TotalLunar
| EC_PartialLunar
| EC_TotalSolar
| EC_AnnularSolar
| EC_PartialSolar.

Definition eclipse_category_code (c : EclipseCategory) : nat :=
  match c with
  | EC_TotalLunar => 0
  | EC_PartialLunar => 1
  | EC_TotalSolar => 2
  | EC_AnnularSolar => 3
  | EC_PartialSolar => 4
  end.

Record HistoricalEclipse := mkHistoricalEclipse {
  he_year : Z;
  he_month : Z;
  he_day : Z;
  he_category : EclipseCategory;
  he_saros_series : Z;
  he_saros_member : Z;
  he_magnitude : Q;
  he_visible_mediterranean : bool
}.

Inductive DialGlyph : Set :=
| Glyph_Sigma
| Glyph_Eta
| Glyph_SigmaTotal
| Glyph_EtaAnnular
| Glyph_Empty.

Definition glyph_code (g : DialGlyph) : nat :=
  match g with
  | Glyph_Sigma => 0
  | Glyph_Eta => 1
  | Glyph_SigmaTotal => 2
  | Glyph_EtaAnnular => 3
  | Glyph_Empty => 4
  end.

Definition category_matches_glyph (cat : EclipseCategory) (g : DialGlyph) : bool :=
  match cat, g with
  | EC_TotalLunar, Glyph_Sigma => true
  | EC_TotalLunar, Glyph_SigmaTotal => true
  | EC_PartialLunar, Glyph_Sigma => true
  | EC_TotalSolar, Glyph_Eta => true
  | EC_AnnularSolar, Glyph_Eta => true
  | EC_AnnularSolar, Glyph_EtaAnnular => true
  | EC_PartialSolar, Glyph_Eta => true
  | _, _ => false
  end.

Definition glyph_at_cell (cell : Z) : DialGlyph :=
  if (cell =? 0)%Z then Glyph_SigmaTotal
  else if (cell =? 6)%Z then Glyph_Sigma
  else if (cell =? 12)%Z then Glyph_Eta
  else if (cell =? 17)%Z then Glyph_Sigma
  else Glyph_Empty.

Definition eclipse_may_205_bc : HistoricalEclipse :=
  mkHistoricalEclipse (-204) 5 12 EC_TotalLunar 44 34 (165 # 100) true.

Definition eclipse_nov_205_bc : HistoricalEclipse :=
  mkHistoricalEclipse (-204) 11 23 EC_TotalLunar 49 32 (142 # 100) true.

Definition eclipse_may_204_bc : HistoricalEclipse :=
  mkHistoricalEclipse (-203) 5 1 EC_PartialSolar 44 35 (34 # 100) true.

Definition eclipse_oct_204_bc : HistoricalEclipse :=
  mkHistoricalEclipse (-203) 10 26 EC_TotalLunar 59 27 (136 # 100) true.

Definition eclipse_mar_187_bc : HistoricalEclipse :=
  mkHistoricalEclipse (-186) 3 14 EC_TotalLunar 44 35 (161 # 100) true.

Definition eclipse_jun_178_bc : HistoricalEclipse :=
  mkHistoricalEclipse (-177) 6 21 EC_TotalLunar 56 36 (156 # 100) true.

Definition eclipse_database : list HistoricalEclipse :=
  [ eclipse_may_205_bc;
    eclipse_nov_205_bc;
    eclipse_may_204_bc;
    eclipse_oct_204_bc;
    eclipse_mar_187_bc;
    eclipse_jun_178_bc ].

Fixpoint count_total_lunar (es : list HistoricalEclipse) : nat :=
  match es with
  | [] => 0%nat
  | eclipse :: rest =>
      let count_here :=
        match he_category eclipse with
        | EC_TotalLunar => 1%nat
        | _ => 0%nat
        end in
      count_here + count_total_lunar rest
  end.

Fixpoint count_visible_total_lunar (es : list HistoricalEclipse) : nat :=
  match es with
  | [] => 0%nat
  | eclipse :: rest =>
      let count_here :=
        match he_category eclipse with
        | EC_TotalLunar =>
            if he_visible_mediterranean eclipse then 1%nat else 0%nat
        | _ => 0%nat
        end in
      count_here + count_visible_total_lunar rest
  end.

Fixpoint visible_series_checksum (es : list HistoricalEclipse) : nat :=
  match es with
  | [] => 0%nat
  | eclipse :: rest =>
      let term :=
        if he_visible_mediterranean eclipse
        then Z.to_nat (Z.abs (he_saros_series eclipse))
        else 0%nat in
      term + visible_series_checksum rest
  end.

Definition months_from_epoch
    (epoch_year eclipse_year : Z)
    (epoch_month eclipse_month : Z)
    : Z :=
  let year_diff := (epoch_year - eclipse_year)%Z in
  let month_diff := (eclipse_month - epoch_month)%Z in
  (year_diff * 12 + month_diff)%Z.

Definition saros_cell (epoch_year epoch_month : Z) (e : HistoricalEclipse) : Z :=
  let months := months_from_epoch epoch_year (he_year e) epoch_month (he_month e) in
  (months mod 223)%Z.

Definition saros_dial_at_month (start_cell : Z) (months : Z) : Z :=
  ((start_cell + months) mod 223)%Z.

Record EpochReading := mkEpochReading {
  reading_state : MechanismState;
  reading_eclipse : HistoricalEclipse;
  reading_cell : Z;
  reading_glyph : DialGlyph
}.

Definition build_epoch_reading
    (epoch_year epoch_month : Z)
    (e : HistoricalEclipse)
    : EpochReading :=
  let cell := saros_cell epoch_year epoch_month e in
  mkEpochReading
    (state_at_cell cell)
    e
    cell
    (glyph_at_cell cell).

Definition reading_matches (reading : EpochReading) : bool :=
  category_matches_glyph
    (he_category (reading_eclipse reading))
    (reading_glyph reading).

Definition reading_phase_code (reading : EpochReading) : nat :=
  phase_code (predict_moon_phase_from_state (reading_state reading)).

Definition reading_zodiac_code (reading : EpochReading) : nat :=
  zodiac_code (predict_zodiac_sign (reading_state reading)).

Definition epoch_eclipse_at_cell_0
    (epoch_year epoch_month : Z)
    (e : HistoricalEclipse)
    : Prop :=
  saros_cell epoch_year epoch_month e = 0%Z.

Definition epoch_in_saros_series_44 (e : HistoricalEclipse) : Prop :=
  he_saros_series e = 44%Z.

Definition epoch_eclipse_visible (e : HistoricalEclipse) : Prop :=
  he_visible_mediterranean e = true.

Definition epoch_eclipse_is_total_lunar (e : HistoricalEclipse) : Prop :=
  he_category e = EC_TotalLunar.

Record ValidEpoch := mkValidEpoch {
  ve_year : Z;
  ve_month : Z;
  ve_eclipse : HistoricalEclipse;
  ve_cell_0 : epoch_eclipse_at_cell_0 ve_year ve_month ve_eclipse;
  ve_series_44 : epoch_in_saros_series_44 ve_eclipse;
  ve_visible : epoch_eclipse_visible ve_eclipse;
  ve_total_lunar : epoch_eclipse_is_total_lunar ve_eclipse
}.

Definition epoch_205_bc_valid : ValidEpoch.
Proof.
  refine (mkValidEpoch (-204) 5 eclipse_may_205_bc _ _ _ _).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Definition sample_epoch_reading : EpochReading :=
  build_epoch_reading (ve_year epoch_205_bc_valid)
    (ve_month epoch_205_bc_valid)
    (ve_eclipse epoch_205_bc_valid).

Definition phase_code_after_steps (n : nat) : nat :=
  phase_code (predict_moon_phase_from_state (step_n n initial_state)).

Definition zodiac_code_after_steps (n : nat) : nat :=
  zodiac_code (predict_zodiac_sign (step_n n initial_state)).

Definition sample_total_lunar_count : nat :=
  count_total_lunar eclipse_database.

Definition sample_total_lunar_visible_count : nat :=
  count_visible_total_lunar eclipse_database.

Definition sample_visible_series_checksum : nat :=
  visible_series_checksum eclipse_database.

Definition sample_epoch_cell_zero : bool :=
  Z.eqb (reading_cell sample_epoch_reading) 0.

Definition sample_epoch_glyph_match : bool :=
  reading_matches sample_epoch_reading.

Definition sample_epoch_phase_code : nat :=
  reading_phase_code sample_epoch_reading.

Definition sample_epoch_zodiac_code : nat :=
  reading_zodiac_code sample_epoch_reading.

Definition sample_valid_epoch_visible : bool :=
  he_visible_mediterranean (ve_eclipse epoch_205_bc_valid).

Definition sample_valid_epoch_series_44 : bool :=
  Z.eqb (he_saros_series (ve_eclipse epoch_205_bc_valid)) 44.

Definition sample_valid_epoch_magnitude_ge_one : bool :=
  Qle_bool (1 # 1) (he_magnitude (ve_eclipse epoch_205_bc_valid)).

Definition sample_step_roundtrip_saros : bool :=
  Z.eqb (saros_dial (step_reverse (step initial_state))) 0.

Definition sample_olympiad_year_is_one_after_4 : bool :=
  Z.eqb (predict_olympiad_year (step_n 4 initial_state)) 1.

Definition sample_eclipse_possible_after_6 : bool :=
  eclipse_possible_at_dial (saros_dial (step_n 6 initial_state)).

Definition sample_epoch_178_misaligned : bool :=
  negb (Z.eqb (saros_cell (-204) 5 eclipse_jun_178_bc) 0).

End EpochCellGlyphTraceCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "epoch_cell_glyph_trace" EpochCellGlyphTraceCase.
