#include <validated_pump_delivery_trace.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool PeanoNat::eqb(const unsigned int n,
                                         const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      unsigned int _x = m - 1;
      return false;
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::eqb(n_, m_);
    }
  }
}

__attribute__((pure)) bool PeanoNat::leb(const unsigned int n,
                                         const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::leb(n_, m_);
    }
  }
}

__attribute__((pure)) bool PeanoNat::ltb(const unsigned int n,
                                         const unsigned int m) {
  return PeanoNat::leb((std::move(n) + 1), m);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
PeanoNat::divmod(const unsigned int x, const unsigned int y,
                 const unsigned int q, const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return PeanoNat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return PeanoNat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

__attribute__((pure)) unsigned int PeanoNat::div(const unsigned int x,
                                                 const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return PeanoNat::divmod(x, y_, 0u, y_).first;
  }
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::bg_in_meter_range(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> &bg) {
  return (PeanoNat::leb(BG_METER_MIN, bg->mg_dL_val) &&
          PeanoNat::leb(bg->mg_dL_val, BG_METER_MAX));
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::carbs_reasonable(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Grams> &carbs) {
  return PeanoNat::leb(carbs->grams_val, CARBS_SANITY_MAX);
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::isf_activity_modifier(
    const ValidatedPumpDeliveryTraceCase::ActivityState state) {
  switch (state) {
  case ActivityState::e_ACTIVITY_NORMAL: {
    return 100u;
  }
  case ActivityState::e_ACTIVITY_LIGHTEXERCISE: {
    return 110u;
  }
  case ActivityState::e_ACTIVITY_MODERATEEXERCISE: {
    return 130u;
  }
  case ActivityState::e_ACTIVITY_INTENSEEXERCISE: {
    return 150u;
  }
  case ActivityState::e_ACTIVITY_ILLNESS: {
    return 80u;
  }
  case ActivityState::e_ACTIVITY_STRESS: {
    return 90u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::icr_activity_modifier(
    const ValidatedPumpDeliveryTraceCase::ActivityState state) {
  switch (state) {
  case ActivityState::e_ACTIVITY_NORMAL: {
    return 100u;
  }
  case ActivityState::e_ACTIVITY_LIGHTEXERCISE: {
    return 110u;
  }
  case ActivityState::e_ACTIVITY_MODERATEEXERCISE: {
    return 125u;
  }
  case ActivityState::e_ACTIVITY_INTENSEEXERCISE: {
    return 140u;
  }
  case ActivityState::e_ACTIVITY_ILLNESS: {
    return 85u;
  }
  case ActivityState::e_ACTIVITY_STRESS: {
    return 95u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Minutes
ValidatedPumpDeliveryTraceCase::peak_time(
    const ValidatedPumpDeliveryTraceCase::InsulinType itype,
    const unsigned int _x) {
  switch (itype) {
  case InsulinType::e_INSULIN_HUMALOG: {
    return 75u;
  }
  case InsulinType::e_INSULIN_ASPART: {
    return 70u;
  }
  case InsulinType::e_INSULIN_LISPRO: {
    return 75u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::div_ceil(const unsigned int a,
                                         const unsigned int b) {
  if (PeanoNat::eqb(b, 0u)) {
    return 0u;
  } else {
    return PeanoNat::div(((((a + b) - 1u) > (a + b) ? 0 : ((a + b) - 1u))), b);
  }
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::event_time_valid(
    const unsigned int now,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent> &event) {
  return PeanoNat::leb(event->be_time_minutes, now);
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::history_times_valid(
    const unsigned int now,
    const std::shared_ptr<
        List<std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>>
        &events) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>::Nil
                 _args) -> bool { return true; },
          [&](const typename List<
              std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>::Cons
                  _args) -> bool {
            return (event_time_valid(now, _args.d_a0) &&
                    history_times_valid(now, _args.d_a1));
          }},
      events->v());
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::history_sorted_from(
    const unsigned int prev,
    const std::shared_ptr<
        List<std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>>
        &events) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>::Nil
                 _args) -> bool { return true; },
          [&](const typename List<
              std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>::Cons
                  _args) -> bool {
            return (
                PeanoNat::leb(_args.d_a0->be_time_minutes, prev) &&
                history_sorted_from(_args.d_a0->be_time_minutes, _args.d_a1));
          }},
      events->v());
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::history_sorted_desc(
    const std::shared_ptr<
        List<std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>>
        &events) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>::Nil
                 _args) -> bool { return true; },
          [](const typename List<
              std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>::Cons
                 _args) -> bool {
            return history_sorted_from(_args.d_a0->be_time_minutes, _args.d_a1);
          }},
      events->v());
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::history_valid(
    const unsigned int now,
    const std::shared_ptr<
        List<std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>>
        &events) {
  return (history_times_valid(now, events) && history_sorted_desc(events));
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::bilinear_iob_fraction(
    const unsigned int elapsed, const unsigned int dia,
    const ValidatedPumpDeliveryTraceCase::InsulinType itype) {
  unsigned int pt = peak_time(itype, dia);
  if (PeanoNat::eqb(dia, 0u)) {
    return 0u;
  } else {
    if (PeanoNat::leb(dia, elapsed)) {
      return 0u;
    } else {
      if (PeanoNat::eqb(pt, 0u)) {
        return 0u;
      } else {
        if (PeanoNat::leb(elapsed, pt)) {
          return (
              ((100u - PeanoNat::div((elapsed * 25u), std::move(pt))) > 100u
                   ? 0
                   : (100u - PeanoNat::div((elapsed * 25u), std::move(pt)))));
        } else {
          if (PeanoNat::leb(dia, pt)) {
            return 0u;
          } else {
            return PeanoNat::div(
                ((((dia - elapsed) > dia ? 0 : (dia - elapsed))) * 75u),
                (((dia - std::move(pt)) > dia ? 0 : (dia - std::move(pt)))));
          }
        }
      }
    }
  }
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::bilinear_iob_from_bolus(
    const unsigned int now,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent> &event,
    const unsigned int dia,
    const ValidatedPumpDeliveryTraceCase::InsulinType itype) {
  if (PeanoNat::ltb(now, event->be_time_minutes)) {
    return 0u;
  } else {
    return div_ceil(
        (event->be_dose_twentieths *
         bilinear_iob_fraction((((now - event->be_time_minutes) > now
                                     ? 0
                                     : (now - event->be_time_minutes))),
                               dia, itype)),
        100u);
  }
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::total_bilinear_iob(
    const unsigned int now,
    const std::shared_ptr<
        List<std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>>
        &events,
    const unsigned int dia,
    const ValidatedPumpDeliveryTraceCase::InsulinType itype) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>::Nil
                 _args) -> unsigned int { return 0u; },
          [&](const typename List<
              std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>::Cons
                  _args) -> unsigned int {
            return (bilinear_iob_from_bolus(now, _args.d_a0, dia, itype) +
                    total_bilinear_iob(now, _args.d_a1, dia, itype));
          }},
      events->v());
}

std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL>
ValidatedPumpDeliveryTraceCase::apply_sensor_margin(
    std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> bg,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> &target) {
  if (PeanoNat::leb(target->mg_dL_val, bg->mg_dL_val)) {
    return std::make_shared<ValidatedPumpDeliveryTraceCase::Mg_dL>(Mg_dL{(
        ((bg->mg_dL_val - PeanoNat::div((bg->mg_dL_val * 15u), 100u)) >
                 bg->mg_dL_val
             ? 0
             : (bg->mg_dL_val - PeanoNat::div((bg->mg_dL_val * 15u), 100u))))});
  } else {
    return std::move(bg);
  }
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::adjusted_isf_tenths(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> &bg,
    const unsigned int base_isf_tenths) {
  if (PeanoNat::ltb(bg->mg_dL_val, 250u)) {
    return std::move(base_isf_tenths);
  } else {
    if (PeanoNat::ltb(bg->mg_dL_val, 350u)) {
      return PeanoNat::div((std::move(base_isf_tenths) * 80u), 100u);
    } else {
      return PeanoNat::div((std::move(base_isf_tenths) * 60u), 100u);
    }
  }
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::correction_twentieths_full(
    const unsigned int _x,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> &current_bg,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> &target_bg,
    const unsigned int base_isf_tenths) {
  unsigned int eff_isf = adjusted_isf_tenths(current_bg, base_isf_tenths);
  if (PeanoNat::eqb(eff_isf, 0u)) {
    return 0u;
  } else {
    if (PeanoNat::leb(current_bg->mg_dL_val, target_bg->mg_dL_val)) {
      return 0u;
    } else {
      return PeanoNat::div(
          ((((current_bg->mg_dL_val - target_bg->mg_dL_val) >
                     current_bg->mg_dL_val
                 ? 0
                 : (current_bg->mg_dL_val - target_bg->mg_dL_val))) *
           200u),
          std::move(eff_isf));
    }
  }
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::apply_reverse_correction_twentieths(
    const unsigned int carb,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> &current_bg,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> &target_bg,
    const unsigned int isf_tenths) {
  if (PeanoNat::ltb(current_bg->mg_dL_val, target_bg->mg_dL_val)) {
    unsigned int reverse_drop =
        (((target_bg->mg_dL_val - current_bg->mg_dL_val) > target_bg->mg_dL_val
              ? 0
              : (target_bg->mg_dL_val - current_bg->mg_dL_val)));
    unsigned int reverse_units;
    if (PeanoNat::eqb(isf_tenths, 0u)) {
      reverse_units = 0u;
    } else {
      reverse_units =
          PeanoNat::div((std::move(reverse_drop) * 200u), isf_tenths);
    }
    if (PeanoNat::leb(carb, reverse_units)) {
      return 0u;
    } else {
      return (((std::move(carb) - std::move(reverse_units)) > std::move(carb)
                   ? 0
                   : (std::move(carb) - std::move(reverse_units))));
    }
  } else {
    return std::move(carb);
  }
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::predict_bg_drop_tenths(
    const unsigned int iob_twentieths, const unsigned int isf_tenths) {
  if (PeanoNat::eqb(isf_tenths, 0u)) {
    return 0u;
  } else {
    return PeanoNat::div((iob_twentieths * isf_tenths), 200u);
  }
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::conservative_cob_rise(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Config> &cfg,
    const unsigned int cob_grams) {
  return PeanoNat::div(
      ((cob_grams * cfg->cfg_conservative_cob_absorption_percent) *
       cfg->cfg_bg_rise_per_gram),
      100u);
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::predicted_eventual_bg_tenths(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Config> &cfg,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> &current_bg,
    const unsigned int iob_twentieths, const unsigned int cob_grams,
    const unsigned int isf_tenths) {
  unsigned int drop = predict_bg_drop_tenths(iob_twentieths, isf_tenths);
  unsigned int rise = conservative_cob_rise(cfg, cob_grams);
  unsigned int bg_after_drop;
  if (PeanoNat::leb(current_bg->mg_dL_val, drop)) {
    bg_after_drop = 0u;
  } else {
    bg_after_drop = (((current_bg->mg_dL_val - drop) > current_bg->mg_dL_val
                          ? 0
                          : (current_bg->mg_dL_val - drop)));
  }
  return (std::move(bg_after_drop) + std::move(rise));
}

std::shared_ptr<ValidatedPumpDeliveryTraceCase::SuspendDecision>
ValidatedPumpDeliveryTraceCase::suspend_check_tenths_with_cob(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Config> &cfg,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> &current_bg,
    const unsigned int iob_twentieths, const unsigned int cob_grams,
    const unsigned int isf_tenths, const unsigned int proposed) {
  if (PeanoNat::eqb(isf_tenths, 0u)) {
    return SuspendDecision::suspend_withhold();
  } else {
    unsigned int total_insulin = (iob_twentieths + proposed);
    unsigned int pred = predicted_eventual_bg_tenths(
        cfg, current_bg, std::move(total_insulin), cob_grams, isf_tenths);
    if (PeanoNat::ltb(pred, BG_LEVEL2_HYPO)) {
      return SuspendDecision::suspend_withhold();
    } else {
      if (PeanoNat::ltb(std::move(pred), cfg->cfg_suspend_threshold_mg_dl)) {
        unsigned int rise_from_cob = conservative_cob_rise(cfg, cob_grams);
        unsigned int effective_target;
        if (PeanoNat::leb(cfg->cfg_suspend_threshold_mg_dl, rise_from_cob)) {
          effective_target = 0u;
        } else {
          effective_target =
              (((cfg->cfg_suspend_threshold_mg_dl - rise_from_cob) >
                        cfg->cfg_suspend_threshold_mg_dl
                    ? 0
                    : (cfg->cfg_suspend_threshold_mg_dl - rise_from_cob)));
        }
        unsigned int safe_drop;
        if (PeanoNat::leb(current_bg->mg_dL_val, effective_target)) {
          safe_drop = 0u;
        } else {
          safe_drop = (((current_bg->mg_dL_val - effective_target) >
                                current_bg->mg_dL_val
                            ? 0
                            : (current_bg->mg_dL_val - effective_target)));
        }
        unsigned int safe_insulin =
            PeanoNat::div((std::move(safe_drop) * 200u), isf_tenths);
        if (PeanoNat::leb(safe_insulin, iob_twentieths)) {
          return SuspendDecision::suspend_withhold();
        } else {
          return SuspendDecision::suspend_reduce(
              (((std::move(safe_insulin) - std::move(iob_twentieths)) >
                        std::move(safe_insulin)
                    ? 0
                    : (std::move(safe_insulin) - std::move(iob_twentieths)))));
        }
      } else {
        return SuspendDecision::suspend_none();
      }
    }
  }
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::apply_suspend(
    const unsigned int proposed,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::SuspendDecision>
        &decision) {
  return std::visit(
      Overloaded{
          [&](const typename ValidatedPumpDeliveryTraceCase::SuspendDecision::
                  Suspend_None _args) -> unsigned int {
            return std::move(proposed);
          },
          [&](const typename ValidatedPumpDeliveryTraceCase::SuspendDecision::
                  Suspend_Reduce _args) -> unsigned int {
            if (PeanoNat::leb(proposed, _args.d_a0)) {
              return std::move(proposed);
            } else {
              return _args.d_a0;
            }
          },
          [](const typename ValidatedPumpDeliveryTraceCase::SuspendDecision::
                 Suspend_Withhold _args) -> unsigned int { return 0u; }},
      decision->v());
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::pediatric_max_twentieths(
    const unsigned int weight_kg) {
  return (weight_kg * 10u);
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::cap_pediatric(const unsigned int bolus,
                                              const unsigned int weight_kg) {
  if (PeanoNat::leb(bolus, pediatric_max_twentieths(weight_kg))) {
    return std::move(bolus);
  } else {
    return pediatric_max_twentieths(weight_kg);
  }
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::prec_params_valid(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionParams> &p) {
  return (((((((PeanoNat::leb(20u, p->prec_icr_tenths) &&
                PeanoNat::leb(p->prec_icr_tenths, 1000u)) &&
               PeanoNat::leb(100u, p->prec_isf_tenths)) &&
              PeanoNat::leb(p->prec_isf_tenths, 4000u)) &&
             PeanoNat::leb(BG_HYPO, p->prec_target_bg->mg_dL_val)) &&
            PeanoNat::leb(p->prec_target_bg->mg_dL_val, BG_HYPER)) &&
           PeanoNat::leb(120u, p->prec_dia)) &&
          PeanoNat::leb(p->prec_dia, 360u));
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::carb_bolus_twentieths(
    const unsigned int carbs_g, const unsigned int icr_tenths) {
  if (PeanoNat::eqb(icr_tenths, 0u)) {
    return 0u;
  } else {
    return PeanoNat::div((carbs_g * 200u), icr_tenths);
  }
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::calculate_precision_bolus(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionInput>
        &input,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionParams>
        &params) {
  unsigned int activity_isf = PeanoNat::div(
      (params->prec_isf_tenths * isf_activity_modifier(input->pi_activity)),
      100u);
  unsigned int activity_icr = PeanoNat::div(
      (params->prec_icr_tenths * icr_activity_modifier(input->pi_activity)),
      100u);
  std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL> eff_bg;
  if (input->pi_use_sensor_margin) {
    eff_bg = apply_sensor_margin(input->pi_current_bg, params->prec_target_bg);
  } else {
    eff_bg = input->pi_current_bg;
  }
  unsigned int carb = carb_bolus_twentieths(input->pi_carbs_g->grams_val,
                                            std::move(activity_icr));
  unsigned int carb_adj = apply_reverse_correction_twentieths(
      std::move(carb), eff_bg, params->prec_target_bg, activity_isf);
  unsigned int corr = correction_twentieths_full(
      input->pi_now, std::move(eff_bg), params->prec_target_bg,
      std::move(activity_isf));
  unsigned int iob =
      total_bilinear_iob(input->pi_now, input->pi_bolus_history,
                         params->prec_dia, params->prec_insulin_type);
  unsigned int raw = (std::move(carb_adj) + std::move(corr));
  if (PeanoNat::leb(raw, iob)) {
    return 0u;
  } else {
    return (((std::move(raw) - std::move(iob)) > std::move(raw)
                 ? 0
                 : (std::move(raw) - std::move(iob))));
  }
}

__attribute__((pure)) bool
ValidatedPumpDeliveryTraceCase::time_reasonable(const unsigned int now) {
  return PeanoNat::leb(
      now, Nat::of_num_uint(Uint1::uintdecimal(Uint::d5(Uint::d2(
               Uint::d5(Uint::d6(Uint::d0(Uint::d0(Uint::nil())))))))));
}

__attribute__((pure)) bool
ValidatedPumpDeliveryTraceCase::history_extraction_safe(
    const std::shared_ptr<
        List<std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>>
        &events) {
  return (
      PeanoNat::leb(events->length(), 100u) &&
      events->forallb(
          [](std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent> e) {
            return PeanoNat::leb(e->be_dose_twentieths, 500u);
          }));
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::iob_high_threshold(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::Config> &cfg) {
  return cfg->cfg_iob_high_threshold_twentieths;
}

__attribute__((pure)) bool
ValidatedPumpDeliveryTraceCase::iob_dangerously_high(const unsigned int iob) {
  return PeanoNat::leb(iob_high_threshold(default_config), iob);
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::bolus_too_soon(
    const unsigned int now,
    const std::shared_ptr<
        List<std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>>
        &history) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>::Nil
                 _args) -> bool { return false; },
          [&](const typename List<
              std::shared_ptr<ValidatedPumpDeliveryTraceCase::BolusEvent>>::Cons
                  _args) -> bool {
            if (PeanoNat::ltb(now, _args.d_a0->be_time_minutes)) {
              return false;
            } else {
              return PeanoNat::ltb(
                  (((now - _args.d_a0->be_time_minutes) > now
                        ? 0
                        : (now - _args.d_a0->be_time_minutes))),
                  15u);
            }
          }},
      history->v());
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::cap_twentieths(const unsigned int t) {
  if (PeanoNat::leb(t, 500u)) {
    return std::move(t);
  } else {
    return 500u;
  }
}

std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionResult>
ValidatedPumpDeliveryTraceCase::validated_precision_bolus(
    std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionInput> input,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionParams>
        &params) {
  if (!(prec_params_valid(params))) {
    return PrecisionResult::precerror(prec_error_invalid_params);
  } else {
    if (!((bg_in_meter_range(input->pi_current_bg) &&
           carbs_reasonable(input->pi_carbs_g)))) {
      return PrecisionResult::precerror(prec_error_invalid_input);
    } else {
      if (!(time_reasonable(input->pi_now))) {
        return PrecisionResult::precerror(prec_error_invalid_time);
      } else {
        if (!(history_valid(input->pi_now, input->pi_bolus_history))) {
          return PrecisionResult::precerror(prec_error_invalid_history);
        } else {
          if (!(history_extraction_safe(input->pi_bolus_history))) {
            return PrecisionResult::precerror(prec_error_extraction_unsafe);
          } else {
            if (bolus_too_soon(input->pi_now, input->pi_bolus_history)) {
              return PrecisionResult::precerror(prec_error_stacking);
            } else {
              if (input->pi_fault->fault_blocks_bolus()) {
                return PrecisionResult::precerror(prec_error_fault);
              } else {
                if (PeanoNat::ltb(input->pi_current_bg->mg_dL_val, BG_HYPO)) {
                  return PrecisionResult::precerror(prec_error_hypo);
                } else {
                  unsigned int iob = total_bilinear_iob(
                      input->pi_now, input->pi_bolus_history, params->prec_dia,
                      params->prec_insulin_type);
                  if ((iob_dangerously_high(iob) &&
                       PeanoNat::eqb(input->pi_carbs_g->grams_val, 0u))) {
                    return PrecisionResult::precerror(prec_error_iob_high);
                  } else {
                    unsigned int tdd_current =
                        input->pi_bolus_history->template fold_left<
                            unsigned int>(
                            [=](unsigned int acc,
                                std::shared_ptr<
                                    ValidatedPumpDeliveryTraceCase::BolusEvent>
                                    e) mutable {
                              if ((PeanoNat::leb(
                                       (((input->pi_now - 1440u) > input->pi_now
                                             ? 0
                                             : (input->pi_now - 1440u))),
                                       e->be_time_minutes) &&
                                   PeanoNat::leb(e->be_time_minutes,
                                                 input->pi_now))) {
                                return (acc + e->be_dose_twentieths);
                              } else {
                                return acc;
                              }
                            },
                            0u);
                    unsigned int tdd_limit;
                    if (input->pi_weight_kg.has_value()) {
                      unsigned int w = *input->pi_weight_kg;
                      tdd_limit = (w * ONE_UNIT);
                    } else {
                      tdd_limit = 5000u;
                    }
                    if (PeanoNat::leb(tdd_limit, tdd_current)) {
                      return PrecisionResult::precerror(
                          prec_error_tdd_exceeded);
                    } else {
                      unsigned int raw =
                          calculate_precision_bolus(input, params);
                      unsigned int tdd_capped;
                      if (PeanoNat::leb((raw + tdd_current), tdd_limit)) {
                        tdd_capped = raw;
                      } else {
                        tdd_capped = (((tdd_limit - tdd_current) > tdd_limit
                                           ? 0
                                           : (tdd_limit - tdd_current)));
                      }
                      unsigned int activity_isf = PeanoNat::div(
                          (params->prec_isf_tenths *
                           isf_activity_modifier(input->pi_activity)),
                          100u);
                      std::shared_ptr<ValidatedPumpDeliveryTraceCase::Mg_dL>
                          eff_bg;
                      if (input->pi_use_sensor_margin) {
                        eff_bg = apply_sensor_margin(input->pi_current_bg,
                                                     params->prec_target_bg);
                      } else {
                        eff_bg = input->pi_current_bg;
                      }
                      std::shared_ptr<
                          ValidatedPumpDeliveryTraceCase::SuspendDecision>
                          suspend_decision = suspend_check_tenths_with_cob(
                              default_config, std::move(eff_bg), std::move(iob),
                              input->pi_carbs_g->grams_val,
                              std::move(activity_isf), tdd_capped);
                      unsigned int suspended = apply_suspend(
                          std::move(tdd_capped), std::move(suspend_decision));
                      unsigned int adult_capped =
                          cap_twentieths(std::move(suspended));
                      unsigned int capped;
                      if (input->pi_weight_kg.has_value()) {
                        unsigned int w = *input->pi_weight_kg;
                        capped = cap_pediatric(adult_capped, std::move(w));
                      } else {
                        capped = std::move(adult_capped);
                      }
                      bool was_modified =
                          !(PeanoNat::eqb(std::move(raw), capped));
                      return PrecisionResult::precok(std::move(capped),
                                                     std::move(was_modified));
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

__attribute__((pure))
std::optional<ValidatedPumpDeliveryTraceCase::Insulin_twentieth>
ValidatedPumpDeliveryTraceCase::prec_result_twentieths(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionResult> &r) {
  return std::visit(
      Overloaded{
          [](const typename ValidatedPumpDeliveryTraceCase::PrecisionResult::
                 PrecOK _args) -> std::optional<unsigned int> {
            return std::make_optional<unsigned int>(_args.d_a0);
          },
          [](const typename ValidatedPumpDeliveryTraceCase::PrecisionResult::
                 PrecError _args) -> std::optional<unsigned int> {
            return std::optional<unsigned int>();
          }},
      r->v());
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::mmol_tenths_to_mg_dL(
    const unsigned int mmol_tenths) {
  return PeanoNat::div((mmol_tenths * 18u), 10u);
}

std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionInput>
ValidatedPumpDeliveryTraceCase::convert_mmol_input(
    std::shared_ptr<ValidatedPumpDeliveryTraceCase::MmolPrecisionInput> input) {
  return std::make_shared<ValidatedPumpDeliveryTraceCase::PrecisionInput>(
      PrecisionInput{
          input->mpi_carbs_g,
          std::make_shared<ValidatedPumpDeliveryTraceCase::Mg_dL>(
              Mg_dL{mmol_tenths_to_mg_dL(input->mpi_current_bg_mmol_tenths)}),
          input->mpi_now, input->mpi_bolus_history, input->mpi_activity,
          input->mpi_use_sensor_margin, input->mpi_fault,
          input->mpi_weight_kg});
}

std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionResult>
ValidatedPumpDeliveryTraceCase::validated_mmol_bolus(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::MmolPrecisionInput>
        &input,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionParams>
        &params) {
  return validated_precision_bolus(convert_mmol_input(input), params);
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::round_down_to_increment(
    const unsigned int t, const unsigned int increment) {
  if (PeanoNat::eqb(increment, 0u)) {
    return std::move(t);
  } else {
    return (PeanoNat::div(std::move(t), increment) * increment);
  }
}

__attribute__((pure)) ValidatedPumpDeliveryTraceCase::Insulin_twentieth
ValidatedPumpDeliveryTraceCase::apply_rounding(
    const ValidatedPumpDeliveryTraceCase::RoundingMode mode,
    const unsigned int t) {
  switch (mode) {
  case RoundingMode::e_ROUNDTWENTIETH: {
    return std::move(t);
  }
  case RoundingMode::e_ROUNDTENTH: {
    return round_down_to_increment(std::move(t), 2u);
  }
  case RoundingMode::e_ROUNDHALF: {
    return round_down_to_increment(std::move(t), 10u);
  }
  case RoundingMode::e_ROUNDUNIT: {
    return round_down_to_increment(std::move(t), ONE_UNIT);
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure))
std::optional<ValidatedPumpDeliveryTraceCase::Insulin_twentieth>
ValidatedPumpDeliveryTraceCase::final_delivery(
    const ValidatedPumpDeliveryTraceCase::RoundingMode mode,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionResult>
        &result) {
  return std::visit(
      Overloaded{
          [&](const typename ValidatedPumpDeliveryTraceCase::PrecisionResult::
                  PrecOK _args) -> std::optional<unsigned int> {
            return std::make_optional<unsigned int>(
                apply_rounding(mode, _args.d_a0));
          },
          [](const typename ValidatedPumpDeliveryTraceCase::PrecisionResult::
                 PrecError _args) -> std::optional<unsigned int> {
            return std::optional<unsigned int>();
          }},
      result->v());
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::pump_can_deliver(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PumpState> &state,
    const unsigned int dose) {
  return (((!(state->ps_occlusion_detected) &&
            PeanoNat::leb(dose, state->ps_reservoir_twentieths)) &&
           PeanoNat::leb(dose, 500u)) &&
          PeanoNat::leb(5u, state->ps_battery_percent));
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::reservoir_after_bolus(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PumpState> &state,
    const unsigned int dose) {
  if (PeanoNat::leb(dose, state->ps_reservoir_twentieths)) {
    return (((state->ps_reservoir_twentieths - dose) >
                     state->ps_reservoir_twentieths
                 ? 0
                 : (state->ps_reservoir_twentieths - dose)));
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::option_nat_default(
    const std::optional<unsigned int> x, const unsigned int d) {
  if (x.has_value()) {
    unsigned int v = *x;
    return std::move(v);
  } else {
    return std::move(d);
  }
}

__attribute__((pure)) bool ValidatedPumpDeliveryTraceCase::pump_accepts_result(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PumpState> &pump,
    const ValidatedPumpDeliveryTraceCase::RoundingMode mode,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionResult> &r) {
  if (final_delivery(mode, r).has_value()) {
    unsigned int dose = *final_delivery(mode, r);
    return pump_can_deliver(pump, dose);
  } else {
    return false;
  }
}

__attribute__((pure)) unsigned int
ValidatedPumpDeliveryTraceCase::pump_reservoir_after_result(
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PumpState> &pump,
    const ValidatedPumpDeliveryTraceCase::RoundingMode mode,
    const std::shared_ptr<ValidatedPumpDeliveryTraceCase::PrecisionResult> &r) {
  if (final_delivery(mode, r).has_value()) {
    unsigned int dose = *final_delivery(mode, r);
    return reservoir_after_bolus(pump, dose);
  } else {
    return pump->ps_reservoir_twentieths;
  }
}

__attribute__((pure)) unsigned int Nat::tail_add(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return std::move(m);
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_add(std::move(n0), (m + 1));
  }
}

__attribute__((pure)) unsigned int Nat::tail_addmul(const unsigned int r,
                                                    const unsigned int n,
                                                    const unsigned int m) {
  if (n <= 0) {
    return std::move(r);
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_addmul(Nat::tail_add(m, r), n0, m);
  }
}

__attribute__((pure)) unsigned int Nat::tail_mul(const unsigned int n,
                                                 const unsigned int m) {
  return Nat::tail_addmul(0u, n, m);
}

__attribute__((pure)) unsigned int
Nat::of_uint_acc(const std::shared_ptr<Uint> &d, const unsigned int acc) {
  return std::visit(
      Overloaded{
          [&](const typename Uint::Nil _args) -> unsigned int {
            return std::move(acc);
          },
          [&](const typename Uint::D0 _args) -> unsigned int {
            return Nat::of_uint_acc(_args.d_a0,
                                    Nat::tail_mul(10u, std::move(acc)));
          },
          [&](const typename Uint::D1 _args) -> unsigned int {
            return Nat::of_uint_acc(_args.d_a0,
                                    (Nat::tail_mul(10u, std::move(acc)) + 1));
          },
          [&](const typename Uint::D2 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0, ((Nat::tail_mul(10u, std::move(acc)) + 1) + 1));
          },
          [&](const typename Uint::D3 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1));
          },
          [&](const typename Uint::D4 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                ((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1));
          },
          [&](const typename Uint::D5 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                 1));
          },
          [&](const typename Uint::D6 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                ((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                  1) +
                 1));
          },
          [&](const typename Uint::D7 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint::D8 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                ((((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint::D9 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          }},
      d->v());
}

__attribute__((pure)) unsigned int
Nat::of_uint(const std::shared_ptr<Uint> &d) {
  return Nat::of_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int
Nat::of_hex_uint_acc(const std::shared_ptr<Uint0> &d, const unsigned int acc) {
  return std::visit(
      Overloaded{
          [&](const typename Uint0::Nil0 _args) -> unsigned int {
            return std::move(acc);
          },
          [&](const typename Uint0::D10 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(_args.d_a0,
                                        Nat::tail_mul(16u, std::move(acc)));
          },
          [&](const typename Uint0::D11 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0, (Nat::tail_mul(16u, std::move(acc)) + 1));
          },
          [&](const typename Uint0::D12 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0, ((Nat::tail_mul(16u, std::move(acc)) + 1) + 1));
          },
          [&](const typename Uint0::D13 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1));
          },
          [&](const typename Uint0::D14 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1));
          },
          [&](const typename Uint0::D15 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                 1));
          },
          [&](const typename Uint0::D16 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::D17 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::D18 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::D19 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Da _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Db _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Dc _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Dd _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
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
          },
          [&](const typename Uint0::De _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) +
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
                  1) +
                 1));
          },
          [&](const typename Uint0::Df _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) +
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
                   1) +
                  1) +
                 1));
          }},
      d->v());
}

__attribute__((pure)) unsigned int
Nat::of_hex_uint(const std::shared_ptr<Uint0> &d) {
  return Nat::of_hex_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int
Nat::of_num_uint(const std::shared_ptr<Uint1> &d) {
  return std::visit(
      Overloaded{[](const typename Uint1::UIntDecimal _args) -> unsigned int {
                   return Nat::of_uint(_args.d_u);
                 },
                 [](const typename Uint1::UIntHexadecimal _args)
                     -> unsigned int { return Nat::of_hex_uint(_args.d_u); }},
      d->v());
}
