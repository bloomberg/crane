#include "validated_pump_delivery_trace.h"

bool ValidatedPumpDeliveryTraceCase::bg_in_meter_range(
    const ValidatedPumpDeliveryTraceCase::Mg_dL &bg) {
  return (BG_METER_MIN <= bg.mg_dL_val && bg.mg_dL_val <= BG_METER_MAX);
}

bool ValidatedPumpDeliveryTraceCase::carbs_reasonable(
    const ValidatedPumpDeliveryTraceCase::Grams &carbs) {
  return carbs.grams_val <= CARBS_SANITY_MAX;
}

uint64_t ValidatedPumpDeliveryTraceCase::isf_activity_modifier(
    ValidatedPumpDeliveryTraceCase::ActivityState state) {
  switch (state) {
  case ActivityState::ACTIVITY_NORMAL: {
    return UINT64_C(100);
  }
  case ActivityState::ACTIVITY_LIGHTEXERCISE: {
    return UINT64_C(110);
  }
  case ActivityState::ACTIVITY_MODERATEEXERCISE: {
    return UINT64_C(130);
  }
  case ActivityState::ACTIVITY_INTENSEEXERCISE: {
    return UINT64_C(150);
  }
  case ActivityState::ACTIVITY_ILLNESS: {
    return UINT64_C(80);
  }
  case ActivityState::ACTIVITY_STRESS: {
    return UINT64_C(90);
  }
  default:
    std::unreachable();
  }
}

uint64_t ValidatedPumpDeliveryTraceCase::icr_activity_modifier(
    ValidatedPumpDeliveryTraceCase::ActivityState state) {
  switch (state) {
  case ActivityState::ACTIVITY_NORMAL: {
    return UINT64_C(100);
  }
  case ActivityState::ACTIVITY_LIGHTEXERCISE: {
    return UINT64_C(110);
  }
  case ActivityState::ACTIVITY_MODERATEEXERCISE: {
    return UINT64_C(125);
  }
  case ActivityState::ACTIVITY_INTENSEEXERCISE: {
    return UINT64_C(140);
  }
  case ActivityState::ACTIVITY_ILLNESS: {
    return UINT64_C(85);
  }
  case ActivityState::ACTIVITY_STRESS: {
    return UINT64_C(95);
  }
  default:
    std::unreachable();
  }
}

ValidatedPumpDeliveryTraceCase::Minutes
ValidatedPumpDeliveryTraceCase::peak_time(
    ValidatedPumpDeliveryTraceCase::InsulinType itype, uint64_t) {
  switch (itype) {
  case InsulinType::INSULIN_ASPART: {
    return UINT64_C(70);
  }
  default: {
    return UINT64_C(75);
  }
  }
}

uint64_t ValidatedPumpDeliveryTraceCase::div_ceil(uint64_t a, uint64_t b) {
  if (b == UINT64_C(0)) {
    return UINT64_C(0);
  } else {
    return (
        b ? ((((a + b) - UINT64_C(1)) > (a + b) ? 0
                                                : ((a + b) - UINT64_C(1)))) /
                b
          : 0);
  }
}

bool ValidatedPumpDeliveryTraceCase::event_time_valid(
    uint64_t now, const ValidatedPumpDeliveryTraceCase::BolusEvent &event) {
  return event.be_time_minutes <= now;
}

bool ValidatedPumpDeliveryTraceCase::history_times_valid(
    uint64_t now,
    const List<ValidatedPumpDeliveryTraceCase::BolusEvent> &events) {
  if (std::holds_alternative<
          typename List<ValidatedPumpDeliveryTraceCase::BolusEvent>::Nil>(
          events.v())) {
    return true;
  } else {
    const auto &[a0, a1] = std::get<
        typename List<ValidatedPumpDeliveryTraceCase::BolusEvent>::Cons>(
        events.v());
    return (event_time_valid(now, a0) && history_times_valid(now, *a1));
  }
}

bool ValidatedPumpDeliveryTraceCase::history_sorted_from(
    uint64_t prev,
    const List<ValidatedPumpDeliveryTraceCase::BolusEvent> &events) {
  if (std::holds_alternative<
          typename List<ValidatedPumpDeliveryTraceCase::BolusEvent>::Nil>(
          events.v())) {
    return true;
  } else {
    const auto &[a0, a1] = std::get<
        typename List<ValidatedPumpDeliveryTraceCase::BolusEvent>::Cons>(
        events.v());
    return (a0.be_time_minutes <= prev &&
            history_sorted_from(a0.be_time_minutes, *a1));
  }
}

bool ValidatedPumpDeliveryTraceCase::history_sorted_desc(
    const List<ValidatedPumpDeliveryTraceCase::BolusEvent> &events) {
  if (std::holds_alternative<
          typename List<ValidatedPumpDeliveryTraceCase::BolusEvent>::Nil>(
          events.v())) {
    return true;
  } else {
    const auto &[a0, a1] = std::get<
        typename List<ValidatedPumpDeliveryTraceCase::BolusEvent>::Cons>(
        events.v());
    return history_sorted_from(a0.be_time_minutes, *a1);
  }
}

bool ValidatedPumpDeliveryTraceCase::history_valid(
    uint64_t now,
    const List<ValidatedPumpDeliveryTraceCase::BolusEvent> &events) {
  return (history_times_valid(now, events) && history_sorted_desc(events));
}

uint64_t ValidatedPumpDeliveryTraceCase::bilinear_iob_fraction(
    uint64_t elapsed, uint64_t dia,
    ValidatedPumpDeliveryTraceCase::InsulinType itype) {
  uint64_t pt = peak_time(itype, dia);
  if (dia == UINT64_C(0)) {
    return UINT64_C(0);
  } else {
    if (dia <= elapsed) {
      return UINT64_C(0);
    } else {
      if (pt == UINT64_C(0)) {
        return UINT64_C(0);
      } else {
        if (elapsed <= pt) {
          return (((UINT64_C(100) - (pt ? (elapsed * UINT64_C(25)) / pt : 0)) >
                           UINT64_C(100)
                       ? 0
                       : (UINT64_C(100) -
                          (pt ? (elapsed * UINT64_C(25)) / pt : 0))));
        } else {
          if (dia <= pt) {
            return UINT64_C(0);
          } else {
            return ((((dia - pt) > dia ? 0 : (dia - pt)))
                        ? ((((dia - elapsed) > dia ? 0 : (dia - elapsed))) *
                           UINT64_C(75)) /
                              (((dia - pt) > dia ? 0 : (dia - pt)))
                        : 0);
          }
        }
      }
    }
  }
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::bilinear_iob_from_bolus(
    uint64_t now, const ValidatedPumpDeliveryTraceCase::BolusEvent &event,
    uint64_t dia, ValidatedPumpDeliveryTraceCase::InsulinType itype) {
  if (now < event.be_time_minutes) {
    return UINT64_C(0);
  } else {
    return div_ceil(
        (event.be_dose_twentieths *
         bilinear_iob_fraction((((now - event.be_time_minutes) > now
                                     ? 0
                                     : (now - event.be_time_minutes))),
                               dia, itype)),
        UINT64_C(100));
  }
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::total_bilinear_iob(
    uint64_t now,
    const List<ValidatedPumpDeliveryTraceCase::BolusEvent> &events,
    uint64_t dia, ValidatedPumpDeliveryTraceCase::InsulinType itype) {
  if (std::holds_alternative<
          typename List<ValidatedPumpDeliveryTraceCase::BolusEvent>::Nil>(
          events.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<
        typename List<ValidatedPumpDeliveryTraceCase::BolusEvent>::Cons>(
        events.v());
    return (bilinear_iob_from_bolus(now, a0, dia, itype) +
            total_bilinear_iob(now, *a1, dia, itype));
  }
}

ValidatedPumpDeliveryTraceCase::Mg_dL
ValidatedPumpDeliveryTraceCase::apply_sensor_margin(
    ValidatedPumpDeliveryTraceCase::Mg_dL bg,
    const ValidatedPumpDeliveryTraceCase::Mg_dL &target) {
  if (target.mg_dL_val <= bg.mg_dL_val) {
    return Mg_dL{(
        ((bg.mg_dL_val -
          (UINT64_C(100) ? (bg.mg_dL_val * UINT64_C(15)) / UINT64_C(100) : 0)) >
                 bg.mg_dL_val
             ? 0
             : (bg.mg_dL_val -
                (UINT64_C(100) ? (bg.mg_dL_val * UINT64_C(15)) / UINT64_C(100)
                               : 0))))};
  } else {
    return bg;
  }
}

uint64_t ValidatedPumpDeliveryTraceCase::adjusted_isf_tenths(
    const ValidatedPumpDeliveryTraceCase::Mg_dL &bg, uint64_t base_isf_tenths) {
  if (bg.mg_dL_val < UINT64_C(250)) {
    return base_isf_tenths;
  } else {
    if (bg.mg_dL_val < UINT64_C(350)) {
      return (UINT64_C(100) ? (base_isf_tenths * UINT64_C(80)) / UINT64_C(100)
                            : 0);
    } else {
      return (UINT64_C(100) ? (base_isf_tenths * UINT64_C(60)) / UINT64_C(100)
                            : 0);
    }
  }
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::correction_twentieths_full(
    uint64_t, const ValidatedPumpDeliveryTraceCase::Mg_dL &current_bg,
    const ValidatedPumpDeliveryTraceCase::Mg_dL &target_bg,
    uint64_t base_isf_tenths) {
  uint64_t eff_isf = adjusted_isf_tenths(current_bg, base_isf_tenths);
  if (eff_isf == UINT64_C(0)) {
    return UINT64_C(0);
  } else {
    if (current_bg.mg_dL_val <= target_bg.mg_dL_val) {
      return UINT64_C(0);
    } else {
      return (eff_isf
                  ? ((((current_bg.mg_dL_val - target_bg.mg_dL_val) >
                               current_bg.mg_dL_val
                           ? 0
                           : (current_bg.mg_dL_val - target_bg.mg_dL_val))) *
                     UINT64_C(200)) /
                        eff_isf
                  : 0);
    }
  }
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::apply_reverse_correction_twentieths(
    uint64_t carb, const ValidatedPumpDeliveryTraceCase::Mg_dL &current_bg,
    const ValidatedPumpDeliveryTraceCase::Mg_dL &target_bg,
    uint64_t isf_tenths) {
  if (current_bg.mg_dL_val < target_bg.mg_dL_val) {
    uint64_t reverse_drop =
        (((target_bg.mg_dL_val - current_bg.mg_dL_val) > target_bg.mg_dL_val
              ? 0
              : (target_bg.mg_dL_val - current_bg.mg_dL_val)));
    uint64_t reverse_units;
    if (isf_tenths == UINT64_C(0)) {
      reverse_units = UINT64_C(0);
    } else {
      reverse_units =
          (isf_tenths ? (reverse_drop * UINT64_C(200)) / isf_tenths : 0);
    }
    if (carb <= reverse_units) {
      return UINT64_C(0);
    } else {
      return (((carb - reverse_units) > carb ? 0 : (carb - reverse_units)));
    }
  } else {
    return carb;
  }
}

uint64_t
ValidatedPumpDeliveryTraceCase::predict_bg_drop_tenths(uint64_t iob_twentieths,
                                                       uint64_t isf_tenths) {
  if (isf_tenths == UINT64_C(0)) {
    return UINT64_C(0);
  } else {
    return (UINT64_C(200) ? (iob_twentieths * isf_tenths) / UINT64_C(200) : 0);
  }
}

uint64_t ValidatedPumpDeliveryTraceCase::conservative_cob_rise(
    const ValidatedPumpDeliveryTraceCase::Config &cfg, uint64_t cob_grams) {
  return (UINT64_C(100)
              ? ((cob_grams * cfg.cfg_conservative_cob_absorption_percent) *
                 cfg.cfg_bg_rise_per_gram) /
                    UINT64_C(100)
              : 0);
}

uint64_t ValidatedPumpDeliveryTraceCase::predicted_eventual_bg_tenths(
    const ValidatedPumpDeliveryTraceCase::Config &cfg,
    const ValidatedPumpDeliveryTraceCase::Mg_dL &current_bg,
    uint64_t iob_twentieths, uint64_t cob_grams, uint64_t isf_tenths) {
  uint64_t drop = predict_bg_drop_tenths(iob_twentieths, isf_tenths);
  uint64_t rise = conservative_cob_rise(cfg, cob_grams);
  uint64_t bg_after_drop;
  if (current_bg.mg_dL_val <= drop) {
    bg_after_drop = UINT64_C(0);
  } else {
    bg_after_drop = (((current_bg.mg_dL_val - drop) > current_bg.mg_dL_val
                          ? 0
                          : (current_bg.mg_dL_val - drop)));
  }
  return (bg_after_drop + rise);
}

ValidatedPumpDeliveryTraceCase::SuspendDecision
ValidatedPumpDeliveryTraceCase::suspend_check_tenths_with_cob(
    const ValidatedPumpDeliveryTraceCase::Config &cfg,
    const ValidatedPumpDeliveryTraceCase::Mg_dL &current_bg,
    uint64_t iob_twentieths, uint64_t cob_grams, uint64_t isf_tenths,
    uint64_t proposed) {
  if (isf_tenths == UINT64_C(0)) {
    return SuspendDecision::suspend_withhold();
  } else {
    uint64_t total_insulin = (iob_twentieths + proposed);
    uint64_t pred = predicted_eventual_bg_tenths(cfg, current_bg, total_insulin,
                                                 cob_grams, isf_tenths);
    if (pred < BG_LEVEL2_HYPO) {
      return SuspendDecision::suspend_withhold();
    } else {
      if (pred < cfg.cfg_suspend_threshold_mg_dl) {
        uint64_t rise_from_cob = conservative_cob_rise(cfg, cob_grams);
        uint64_t effective_target;
        if (cfg.cfg_suspend_threshold_mg_dl <= rise_from_cob) {
          effective_target = UINT64_C(0);
        } else {
          effective_target =
              (((cfg.cfg_suspend_threshold_mg_dl - rise_from_cob) >
                        cfg.cfg_suspend_threshold_mg_dl
                    ? 0
                    : (cfg.cfg_suspend_threshold_mg_dl - rise_from_cob)));
        }
        uint64_t safe_drop;
        if (current_bg.mg_dL_val <= effective_target) {
          safe_drop = UINT64_C(0);
        } else {
          safe_drop =
              (((current_bg.mg_dL_val - effective_target) > current_bg.mg_dL_val
                    ? 0
                    : (current_bg.mg_dL_val - effective_target)));
        }
        uint64_t safe_insulin =
            (isf_tenths ? (safe_drop * UINT64_C(200)) / isf_tenths : 0);
        if (safe_insulin <= iob_twentieths) {
          return SuspendDecision::suspend_withhold();
        } else {
          return SuspendDecision::suspend_reduce(
              (((safe_insulin - iob_twentieths) > safe_insulin
                    ? 0
                    : (safe_insulin - iob_twentieths))));
        }
      } else {
        return SuspendDecision::suspend_none();
      }
    }
  }
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::apply_suspend(
    uint64_t proposed,
    const ValidatedPumpDeliveryTraceCase::SuspendDecision &decision) {
  if (std::holds_alternative<typename ValidatedPumpDeliveryTraceCase::
                                 SuspendDecision::Suspend_None>(decision.v())) {
    return proposed;
  } else if (std::holds_alternative<typename ValidatedPumpDeliveryTraceCase::
                                        SuspendDecision::Suspend_Reduce>(
                 decision.v())) {
    const auto &[a0] =
        std::get<typename ValidatedPumpDeliveryTraceCase::SuspendDecision::
                     Suspend_Reduce>(decision.v());
    if (proposed <= a0) {
      return proposed;
    } else {
      return a0;
    }
  } else {
    return UINT64_C(0);
  }
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::pediatric_max_twentieths(uint64_t weight_kg) {
  return (weight_kg * UINT64_C(10));
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::cap_pediatric(uint64_t bolus,
                                              uint64_t weight_kg) {
  if (bolus <= pediatric_max_twentieths(weight_kg)) {
    return bolus;
  } else {
    return pediatric_max_twentieths(weight_kg);
  }
}

bool ValidatedPumpDeliveryTraceCase::prec_params_valid(
    const ValidatedPumpDeliveryTraceCase::PrecisionParams &p) {
  return (((((((UINT64_C(20) <= p.prec_icr_tenths &&
                p.prec_icr_tenths <= UINT64_C(1000)) &&
               UINT64_C(100) <= p.prec_isf_tenths) &&
              p.prec_isf_tenths <= UINT64_C(4000)) &&
             BG_HYPO <= p.prec_target_bg.mg_dL_val) &&
            p.prec_target_bg.mg_dL_val <= BG_HYPER) &&
           UINT64_C(120) <= p.prec_dia) &&
          p.prec_dia <= UINT64_C(360));
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::carb_bolus_twentieths(uint64_t carbs_g,
                                                      uint64_t icr_tenths) {
  if (icr_tenths == UINT64_C(0)) {
    return UINT64_C(0);
  } else {
    return (icr_tenths ? (carbs_g * UINT64_C(200)) / icr_tenths : 0);
  }
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::calculate_precision_bolus(
    const ValidatedPumpDeliveryTraceCase::PrecisionInput &input,
    const ValidatedPumpDeliveryTraceCase::PrecisionParams &params) {
  uint64_t activity_isf =
      (UINT64_C(100) ? (params.prec_isf_tenths *
                        isf_activity_modifier(input.pi_activity)) /
                           UINT64_C(100)
                     : 0);
  uint64_t activity_icr =
      (UINT64_C(100) ? (params.prec_icr_tenths *
                        icr_activity_modifier(input.pi_activity)) /
                           UINT64_C(100)
                     : 0);
  ValidatedPumpDeliveryTraceCase::Mg_dL eff_bg;
  if (input.pi_use_sensor_margin) {
    eff_bg = apply_sensor_margin(input.pi_current_bg, params.prec_target_bg);
  } else {
    eff_bg = input.pi_current_bg;
  }
  uint64_t carb =
      carb_bolus_twentieths(input.pi_carbs_g.grams_val, activity_icr);
  uint64_t carb_adj = apply_reverse_correction_twentieths(
      carb, eff_bg, params.prec_target_bg, activity_isf);
  uint64_t corr = correction_twentieths_full(
      input.pi_now, std::move(eff_bg), params.prec_target_bg, activity_isf);
  uint64_t iob = total_bilinear_iob(input.pi_now, input.pi_bolus_history,
                                    params.prec_dia, params.prec_insulin_type);
  uint64_t raw = (carb_adj + corr);
  if (raw <= iob) {
    return UINT64_C(0);
  } else {
    return (((raw - iob) > raw ? 0 : (raw - iob)));
  }
}

bool ValidatedPumpDeliveryTraceCase::time_reasonable(uint64_t now) {
  return now <= UINT64_C(525600);
}

bool ValidatedPumpDeliveryTraceCase::history_extraction_safe(
    const List<ValidatedPumpDeliveryTraceCase::BolusEvent> &events) {
  return (
      events.length() <= UINT64_C(100) &&
      events.forallb([](const ValidatedPumpDeliveryTraceCase::BolusEvent &e) {
        return e.be_dose_twentieths <= UINT64_C(500);
      }));
}

uint64_t ValidatedPumpDeliveryTraceCase::iob_high_threshold(
    const ValidatedPumpDeliveryTraceCase::Config &cfg) {
  return cfg.cfg_iob_high_threshold_twentieths;
}

bool ValidatedPumpDeliveryTraceCase::iob_dangerously_high(uint64_t iob) {
  return iob_high_threshold(default_config) <= iob;
}

bool ValidatedPumpDeliveryTraceCase::bolus_too_soon(
    uint64_t now,
    const List<ValidatedPumpDeliveryTraceCase::BolusEvent> &history) {
  if (std::holds_alternative<
          typename List<ValidatedPumpDeliveryTraceCase::BolusEvent>::Nil>(
          history.v())) {
    return false;
  } else {
    const auto &[a0, a1] = std::get<
        typename List<ValidatedPumpDeliveryTraceCase::BolusEvent>::Cons>(
        history.v());
    if (now < a0.be_time_minutes) {
      return false;
    } else {
      return (((now - a0.be_time_minutes) > now ? 0
                                                : (now - a0.be_time_minutes))) <
             UINT64_C(15);
    }
  }
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::cap_twentieths(uint64_t t) {
  if (t <= UINT64_C(500)) {
    return t;
  } else {
    return UINT64_C(500);
  }
}

ValidatedPumpDeliveryTraceCase::PrecisionResult
ValidatedPumpDeliveryTraceCase::validated_precision_bolus(
    ValidatedPumpDeliveryTraceCase::PrecisionInput input,
    const ValidatedPumpDeliveryTraceCase::PrecisionParams &params) {
  if (!(prec_params_valid(params))) {
    return PrecisionResult::precerror(prec_error_invalid_params);
  } else {
    if (!((bg_in_meter_range(input.pi_current_bg) &&
           carbs_reasonable(input.pi_carbs_g)))) {
      return PrecisionResult::precerror(prec_error_invalid_input);
    } else {
      if (!(time_reasonable(input.pi_now))) {
        return PrecisionResult::precerror(prec_error_invalid_time);
      } else {
        if (!(history_valid(input.pi_now, input.pi_bolus_history))) {
          return PrecisionResult::precerror(prec_error_invalid_history);
        } else {
          if (!(history_extraction_safe(input.pi_bolus_history))) {
            return PrecisionResult::precerror(prec_error_extraction_unsafe);
          } else {
            if (bolus_too_soon(input.pi_now, input.pi_bolus_history)) {
              return PrecisionResult::precerror(prec_error_stacking);
            } else {
              if (input.pi_fault.fault_blocks_bolus()) {
                return PrecisionResult::precerror(prec_error_fault);
              } else {
                if (input.pi_current_bg.mg_dL_val < BG_HYPO) {
                  return PrecisionResult::precerror(prec_error_hypo);
                } else {
                  uint64_t iob = total_bilinear_iob(
                      input.pi_now, input.pi_bolus_history, params.prec_dia,
                      params.prec_insulin_type);
                  if ((iob_dangerously_high(iob) &&
                       input.pi_carbs_g.grams_val == UINT64_C(0))) {
                    return PrecisionResult::precerror(prec_error_iob_high);
                  } else {
                    uint64_t tdd_current =
                        input.pi_bolus_history.template fold_left<uint64_t>(
                            [=](uint64_t acc,
                                const ValidatedPumpDeliveryTraceCase::BolusEvent
                                    &e) mutable {
                              if (((((input.pi_now - UINT64_C(1440)) >
                                             input.pi_now
                                         ? 0
                                         : (input.pi_now - UINT64_C(1440)))) <=
                                       e.be_time_minutes &&
                                   e.be_time_minutes <= input.pi_now)) {
                                return (acc + e.be_dose_twentieths);
                              } else {
                                return acc;
                              }
                            },
                            UINT64_C(0));
                    uint64_t tdd_limit;
                    if (std::move(input).pi_weight_kg.has_value()) {
                      const uint64_t &w = *std::move(input).pi_weight_kg;
                      tdd_limit = (w * ONE_UNIT);
                    } else {
                      tdd_limit = UINT64_C(5000);
                    }
                    if (tdd_limit <= tdd_current) {
                      return PrecisionResult::precerror(
                          prec_error_tdd_exceeded);
                    } else {
                      uint64_t raw = calculate_precision_bolus(input, params);
                      uint64_t tdd_capped;
                      if ((raw + tdd_current) <= tdd_limit) {
                        tdd_capped = raw;
                      } else {
                        tdd_capped = (((tdd_limit - tdd_current) > tdd_limit
                                           ? 0
                                           : (tdd_limit - tdd_current)));
                      }
                      uint64_t activity_isf =
                          (UINT64_C(100)
                               ? (params.prec_isf_tenths *
                                  isf_activity_modifier(input.pi_activity)) /
                                     UINT64_C(100)
                               : 0);
                      ValidatedPumpDeliveryTraceCase::Mg_dL eff_bg;
                      if (input.pi_use_sensor_margin) {
                        eff_bg = apply_sensor_margin(input.pi_current_bg,
                                                     params.prec_target_bg);
                      } else {
                        eff_bg = input.pi_current_bg;
                      }
                      ValidatedPumpDeliveryTraceCase::SuspendDecision
                          suspend_decision = suspend_check_tenths_with_cob(
                              default_config, std::move(eff_bg), iob,
                              input.pi_carbs_g.grams_val, activity_isf,
                              tdd_capped);
                      uint64_t suspended = apply_suspend(
                          tdd_capped, std::move(suspend_decision));
                      uint64_t adult_capped = cap_twentieths(suspended);
                      uint64_t capped;
                      if (std::move(input).pi_weight_kg.has_value()) {
                        const uint64_t &w = *std::move(input).pi_weight_kg;
                        capped = cap_pediatric(adult_capped, w);
                      } else {
                        capped = adult_capped;
                      }
                      bool was_modified = !(raw == capped);
                      return PrecisionResult::precok(capped, was_modified);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

std::optional<ValidatedPumpDeliveryTraceCase::Insulin_twentieth>
ValidatedPumpDeliveryTraceCase::prec_result_twentieths(
    const ValidatedPumpDeliveryTraceCase::PrecisionResult &r) {
  if (std::holds_alternative<
          typename ValidatedPumpDeliveryTraceCase::PrecisionResult::PrecOK>(
          r.v())) {
    const auto &[a0, a1] = std::get<
        typename ValidatedPumpDeliveryTraceCase::PrecisionResult::PrecOK>(
        r.v());
    return std::make_optional<uint64_t>(a0);
  } else {
    return std::optional<uint64_t>();
  }
}

uint64_t
ValidatedPumpDeliveryTraceCase::mmol_tenths_to_mg_dL(uint64_t mmol_tenths) {
  return (UINT64_C(10) ? (mmol_tenths * UINT64_C(18)) / UINT64_C(10) : 0);
}

ValidatedPumpDeliveryTraceCase::PrecisionInput
ValidatedPumpDeliveryTraceCase::convert_mmol_input(
    const ValidatedPumpDeliveryTraceCase::MmolPrecisionInput &input) {
  return PrecisionInput{
      input.mpi_carbs_g,
      Mg_dL{mmol_tenths_to_mg_dL(input.mpi_current_bg_mmol_tenths)},
      input.mpi_now,
      input.mpi_bolus_history,
      input.mpi_activity,
      input.mpi_use_sensor_margin,
      input.mpi_fault,
      input.mpi_weight_kg};
}

ValidatedPumpDeliveryTraceCase::PrecisionResult
ValidatedPumpDeliveryTraceCase::validated_mmol_bolus(
    const ValidatedPumpDeliveryTraceCase::MmolPrecisionInput &input,
    const ValidatedPumpDeliveryTraceCase::PrecisionParams &params) {
  return validated_precision_bolus(convert_mmol_input(input), params);
}

uint64_t
ValidatedPumpDeliveryTraceCase::round_down_to_increment(uint64_t t,
                                                        uint64_t increment) {
  if (increment == UINT64_C(0)) {
    return t;
  } else {
    return ((increment ? t / increment : 0) * increment);
  }
}

ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::apply_rounding(
    ValidatedPumpDeliveryTraceCase::RoundingMode mode, uint64_t t) {
  switch (mode) {
  case RoundingMode::ROUNDTWENTIETH: {
    return t;
  }
  case RoundingMode::ROUNDTENTH: {
    return round_down_to_increment(t, UINT64_C(2));
  }
  case RoundingMode::ROUNDHALF: {
    return round_down_to_increment(t, UINT64_C(10));
  }
  case RoundingMode::ROUNDUNIT: {
    return round_down_to_increment(t, ONE_UNIT);
  }
  default:
    std::unreachable();
  }
}

std::optional<ValidatedPumpDeliveryTraceCase::Insulin_twentieth>
ValidatedPumpDeliveryTraceCase::final_delivery(
    ValidatedPumpDeliveryTraceCase::RoundingMode mode,
    const ValidatedPumpDeliveryTraceCase::PrecisionResult &result) {
  if (std::holds_alternative<
          typename ValidatedPumpDeliveryTraceCase::PrecisionResult::PrecOK>(
          result.v())) {
    const auto &[a0, a1] = std::get<
        typename ValidatedPumpDeliveryTraceCase::PrecisionResult::PrecOK>(
        result.v());
    return std::make_optional<uint64_t>(apply_rounding(mode, a0));
  } else {
    return std::optional<uint64_t>();
  }
}

bool ValidatedPumpDeliveryTraceCase::pump_can_deliver(
    const ValidatedPumpDeliveryTraceCase::PumpState &state, uint64_t dose) {
  return (((!(state.ps_occlusion_detected) &&
            dose <= state.ps_reservoir_twentieths) &&
           dose <= UINT64_C(500)) &&
          UINT64_C(5) <= state.ps_battery_percent);
}

uint64_t ValidatedPumpDeliveryTraceCase::reservoir_after_bolus(
    const ValidatedPumpDeliveryTraceCase::PumpState &state, uint64_t dose) {
  if (dose <= state.ps_reservoir_twentieths) {
    return (
        ((state.ps_reservoir_twentieths - dose) > state.ps_reservoir_twentieths
             ? 0
             : (state.ps_reservoir_twentieths - dose)));
  } else {
    return UINT64_C(0);
  }
}

uint64_t ValidatedPumpDeliveryTraceCase::option_nat_default(
    const std::optional<uint64_t> &x, uint64_t d) {
  if (x.has_value()) {
    const uint64_t &v = *x;
    return v;
  } else {
    return d;
  }
}

bool ValidatedPumpDeliveryTraceCase::pump_accepts_result(
    const ValidatedPumpDeliveryTraceCase::PumpState &pump,
    ValidatedPumpDeliveryTraceCase::RoundingMode mode,
    const ValidatedPumpDeliveryTraceCase::PrecisionResult &r) {
  auto _cs = final_delivery(mode, r);
  if (_cs.has_value()) {
    const uint64_t &dose = *_cs;
    return pump_can_deliver(pump, dose);
  } else {
    return false;
  }
}

uint64_t ValidatedPumpDeliveryTraceCase::pump_reservoir_after_result(
    const ValidatedPumpDeliveryTraceCase::PumpState &pump,
    ValidatedPumpDeliveryTraceCase::RoundingMode mode,
    const ValidatedPumpDeliveryTraceCase::PrecisionResult &r) {
  auto _cs = final_delivery(mode, r);
  if (_cs.has_value()) {
    const uint64_t &dose = *_cs;
    return reservoir_after_bolus(pump, dose);
  } else {
    return pump.ps_reservoir_twentieths;
  }
}

uint64_t Nat::tail_add(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return m;
  } else {
    uint64_t n0 = n - 1;
    return Nat::tail_add(n0, (m + 1));
  }
}

uint64_t Nat::tail_addmul(uint64_t r, uint64_t n, uint64_t m) {
  if (n <= 0) {
    return r;
  } else {
    uint64_t n0 = n - 1;
    return Nat::tail_addmul(Nat::tail_add(m, r), n0, m);
  }
}

uint64_t Nat::tail_mul(uint64_t n, uint64_t m) {
  return Nat::tail_addmul(UINT64_C(0), n, m);
}

uint64_t Nat::of_uint_acc(const Uint &d, uint64_t acc) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return Nat::of_uint_acc(*a0, Nat::tail_mul(UINT64_C(10), acc));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return Nat::of_uint_acc(*a0, (Nat::tail_mul(UINT64_C(10), acc) + 1));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return Nat::of_uint_acc(*a0, ((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return Nat::of_uint_acc(*a0,
                            (((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return Nat::of_uint_acc(
        *a0, ((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return Nat::of_uint_acc(
        *a0, (((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return Nat::of_uint_acc(
        *a0,
        ((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return Nat::of_uint_acc(
        *a0,
        (((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return Nat::of_uint_acc(
        *a0,
        ((((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return Nat::of_uint_acc(
        *a0,
        (((((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  }
}

uint64_t Nat::of_uint(const Uint &d) {
  return Nat::of_uint_acc(d, UINT64_C(0));
}

uint64_t Nat::of_hex_uint_acc(const Uint0 &d, uint64_t acc) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return Nat::of_hex_uint_acc(*a0, Nat::tail_mul(UINT64_C(16), acc));
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return Nat::of_hex_uint_acc(*a0, (Nat::tail_mul(UINT64_C(16), acc) + 1));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return Nat::of_hex_uint_acc(*a0,
                                ((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return Nat::of_hex_uint_acc(
        *a0, (((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return Nat::of_hex_uint_acc(
        *a0, ((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return Nat::of_hex_uint_acc(
        *a0, (((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else {
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  }
}

uint64_t Nat::of_hex_uint(const Uint0 &d) {
  return Nat::of_hex_uint_acc(d, UINT64_C(0));
}

uint64_t Nat::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return Nat::of_uint(u);
  } else {
    const auto &[u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return Nat::of_hex_uint(u);
  }
}
