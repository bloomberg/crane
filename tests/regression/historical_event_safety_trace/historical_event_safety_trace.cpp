#include "historical_event_safety_trace.h"

bool HistoricalEventSafetyTraceCase::is_safe_bool(
    const HistoricalEventSafetyTraceCase::PlantConfig &pconf,
    const HistoricalEventSafetyTraceCase::State &s) {
  return (s.reservoir_level_cm <= pconf.max_reservoir_cm &&
          s.downstream_stage_cm <= pconf.max_downstream_cm);
}

uint64_t HistoricalEventSafetyTraceCase::event_to_inflow(
    const List<HistoricalEventSafetyTraceCase::InflowRecord> &event,
    uint64_t default_inflow, uint64_t t) {
  if (std::holds_alternative<
          typename List<HistoricalEventSafetyTraceCase::InflowRecord>::Nil>(
          event.v())) {
    return default_inflow;
  } else {
    const auto &[a0, a1] = std::get<
        typename List<HistoricalEventSafetyTraceCase::InflowRecord>::Cons>(
        event.v());
    if (t == a0.ir_timestep) {
      return a0.ir_inflow_cm;
    } else {
      return event_to_inflow(*a1, default_inflow, t);
    }
  }
}

bool HistoricalEventSafetyTraceCase::test_passes(
    const HistoricalEventSafetyTraceCase::TestResult &result) {
  return (result.tr_initial_safe && result.tr_final_safe);
}

bool HistoricalEventSafetyTraceCase::all_tests_pass(
    const List<HistoricalEventSafetyTraceCase::TestResult> &results) {
  if (std::holds_alternative<
          typename List<HistoricalEventSafetyTraceCase::TestResult>::Nil>(
          results.v())) {
    return true;
  } else {
    const auto &[a0, a1] = std::get<
        typename List<HistoricalEventSafetyTraceCase::TestResult>::Cons>(
        results.v());
    return (test_passes(a0) && all_tests_pass(*a1));
  }
}

uint64_t HistoricalEventSafetyTraceCase::stage_from_table(
    const List<std::pair<uint64_t, uint64_t>> &tbl, uint64_t base_stage,
    uint64_t out) {
  if (std::holds_alternative<typename List<std::pair<uint64_t, uint64_t>>::Nil>(
          tbl.v())) {
    return base_stage;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(tbl.v());
    const auto &[q, s] = a0;
    uint64_t tail = stage_from_table(*a1, base_stage, out);
    if (out <= q) {
      return s;
    } else {
      return std::max(s, tail);
    }
  }
}

uint64_t HistoricalEventSafetyTraceCase::hist_witness_stage(uint64_t out) {
  return (UINT64_C(2) ? out / UINT64_C(2) : 0);
}

uint64_t HistoricalEventSafetyTraceCase::hist_witness_ctrl(
    const HistoricalEventSafetyTraceCase::State &s, uint64_t) {
  if (UINT64_C(90) <= s.reservoir_level_cm) {
    return UINT64_C(100);
  } else {
    return UINT64_C(50);
  }
}

uint64_t HistoricalEventSafetyTraceCase::hoover_controller(
    const HistoricalEventSafetyTraceCase::State &s, uint64_t) {
  if (UINT64_C(2000) <= s.reservoir_level_cm) {
    return UINT64_C(100);
  } else {
    if (UINT64_C(1900) <= s.reservoir_level_cm) {
      return UINT64_C(75);
    } else {
      if (UINT64_C(1800) <= s.reservoir_level_cm) {
        return UINT64_C(50);
      } else {
        if (UINT64_C(1700) <= s.reservoir_level_cm) {
          return UINT64_C(25);
        } else {
          return UINT64_C(0);
        }
      }
    }
  }
}

uint64_t
HistoricalEventSafetyTraceCase::hoover_stage_from_rating(uint64_t out) {
  return stage_from_table(hoover_rating_table.mrt_table, UINT64_C(20), out);
}

uint64_t HistoricalEventSafetyTraceCase::historical_lookup_1983(uint64_t t) {
  return event_to_inflow(flood_1983_inflows, UINT64_C(0), t);
}

uint64_t HistoricalEventSafetyTraceCase::historical_lookup_2011(uint64_t t) {
  return event_to_inflow(flood_2011_inflows, UINT64_C(0), t);
}

bool HistoricalEventSafetyTraceCase::witness_test_initial_safe_at(uint64_t h) {
  return run_historical_test(hist_witness_plant, flood_1983_inflows,
                             UINT64_C(0), hist_witness_ctrl, hist_witness_stage,
                             hist_witness_initial, h, UINT64_C(1983))
      .tr_initial_safe;
}

uint64_t
HistoricalEventSafetyTraceCase::witness_test_peak_level_at(uint64_t h) {
  return run_historical_test(hist_witness_plant, flood_2011_inflows,
                             UINT64_C(0), hist_witness_ctrl, hist_witness_stage,
                             hist_witness_initial, h, UINT64_C(2011))
      .tr_max_level;
}

uint64_t
HistoricalEventSafetyTraceCase::hoover_controller_sample(uint64_t level) {
  return hoover_controller(State{level, UINT64_C(20), UINT64_C(0)},
                           UINT64_C(0));
}

uint64_t HistoricalEventSafetyTraceCase::hoover_stage_sample(uint64_t _x0) {
  return hoover_stage_from_rating(_x0);
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
