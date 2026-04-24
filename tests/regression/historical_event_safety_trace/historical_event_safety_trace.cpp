#include <historical_event_safety_trace.h>

#include <algorithm>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool HistoricalEventSafetyTraceCase::is_safe_bool(
    const HistoricalEventSafetyTraceCase::PlantConfig &pconf,
    const HistoricalEventSafetyTraceCase::State &s) {
  return (s.reservoir_level_cm <= pconf.max_reservoir_cm &&
          s.downstream_stage_cm <= pconf.max_downstream_cm);
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::event_to_inflow(
    const List<HistoricalEventSafetyTraceCase::InflowRecord> &event,
    unsigned int default_inflow, const unsigned int &t) {
  if (std::holds_alternative<
          typename List<HistoricalEventSafetyTraceCase::InflowRecord>::Nil>(
          event.v())) {
    return default_inflow;
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename List<HistoricalEventSafetyTraceCase::InflowRecord>::Cons>(
        event.v());
    if (t == d_a0.ir_timestep) {
      return d_a0.ir_inflow_cm;
    } else {
      return event_to_inflow(*(d_a1), default_inflow, t);
    }
  }
}

__attribute__((pure)) bool HistoricalEventSafetyTraceCase::test_passes(
    const HistoricalEventSafetyTraceCase::TestResult &result) {
  return (result.tr_initial_safe && result.tr_final_safe);
}

__attribute__((pure)) bool HistoricalEventSafetyTraceCase::all_tests_pass(
    const List<HistoricalEventSafetyTraceCase::TestResult> &results) {
  if (std::holds_alternative<
          typename List<HistoricalEventSafetyTraceCase::TestResult>::Nil>(
          results.v())) {
    return true;
  } else {
    const auto &[d_a0, d_a1] = std::get<
        typename List<HistoricalEventSafetyTraceCase::TestResult>::Cons>(
        results.v());
    return (test_passes(d_a0) && all_tests_pass(*(d_a1)));
  }
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::stage_from_table(
    const List<std::pair<unsigned int, unsigned int>> &tbl,
    unsigned int base_stage, const unsigned int &out) {
  if (std::holds_alternative<
          typename List<std::pair<unsigned int, unsigned int>>::Nil>(tbl.v())) {
    return base_stage;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
            tbl.v());
    const unsigned int &q = d_a0.first;
    const unsigned int &s = d_a0.second;
    unsigned int tail = stage_from_table(*(d_a1), base_stage, out);
    if (out <= q) {
      return s;
    } else {
      return std::max(s, tail);
    }
  }
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hist_witness_stage(const unsigned int &out) {
  return (2u ? out / 2u : 0);
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hist_witness_ctrl(
    const HistoricalEventSafetyTraceCase::State &s, const unsigned int &) {
  if (90u <= s.reservoir_level_cm) {
    return 100u;
  } else {
    return 50u;
  }
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hoover_controller(
    const HistoricalEventSafetyTraceCase::State &s, const unsigned int &) {
  if (2000u <= s.reservoir_level_cm) {
    return 100u;
  } else {
    if (1900u <= s.reservoir_level_cm) {
      return 75u;
    } else {
      if (1800u <= s.reservoir_level_cm) {
        return 50u;
      } else {
        if (1700u <= s.reservoir_level_cm) {
          return 25u;
        } else {
          return 0u;
        }
      }
    }
  }
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hoover_stage_from_rating(
    const unsigned int &out) {
  return stage_from_table(hoover_rating_table.mrt_table, 20u, out);
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::historical_lookup_1983(const unsigned int &t) {
  return event_to_inflow(flood_1983_inflows, 0u, t);
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::historical_lookup_2011(const unsigned int &t) {
  return event_to_inflow(flood_2011_inflows, 0u, t);
}

__attribute__((pure)) bool
HistoricalEventSafetyTraceCase::witness_test_initial_safe_at(
    const unsigned int &h) {
  return run_historical_test(hist_witness_plant, flood_1983_inflows, 0u,
                             hist_witness_ctrl, hist_witness_stage,
                             hist_witness_initial, h, 1983u)
      .tr_initial_safe;
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::witness_test_peak_level_at(
    const unsigned int &h) {
  return run_historical_test(hist_witness_plant, flood_2011_inflows, 0u,
                             hist_witness_ctrl, hist_witness_stage,
                             hist_witness_initial, h, 2011u)
      .tr_max_level;
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hoover_controller_sample(unsigned int level) {
  return hoover_controller(State{level, 20u, 0u}, 0u);
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hoover_stage_sample(const unsigned int &_x0) {
  return hoover_stage_from_rating(_x0);
}

__attribute__((pure)) unsigned int Nat::tail_add(const unsigned int &n,
                                                 unsigned int m) {
  if (n <= 0) {
    return m;
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_add(n0, (m + 1));
  }
}

__attribute__((pure)) unsigned int
Nat::tail_addmul(unsigned int r, const unsigned int &n, const unsigned int &m) {
  if (n <= 0) {
    return r;
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_addmul(Nat::tail_add(m, r), n0, m);
  }
}

__attribute__((pure)) unsigned int Nat::tail_mul(const unsigned int &n,
                                                 const unsigned int &m) {
  return Nat::tail_addmul(0u, n, m);
}

__attribute__((pure)) unsigned int Nat::of_uint_acc(const Uint &d,
                                                    unsigned int acc) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D0>(d.v());
    return Nat::of_uint_acc(*(d_a0), Nat::tail_mul(10u, acc));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D1>(d.v());
    return Nat::of_uint_acc(*(d_a0), (Nat::tail_mul(10u, acc) + 1));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D2>(d.v());
    return Nat::of_uint_acc(*(d_a0), ((Nat::tail_mul(10u, acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D3>(d.v());
    return Nat::of_uint_acc(*(d_a0), (((Nat::tail_mul(10u, acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D4>(d.v());
    return Nat::of_uint_acc(*(d_a0),
                            ((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D5>(d.v());
    return Nat::of_uint_acc(
        *(d_a0), (((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D6>(d.v());
    return Nat::of_uint_acc(
        *(d_a0), ((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D7>(d.v());
    return Nat::of_uint_acc(
        *(d_a0),
        (((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D8>(d.v());
    return Nat::of_uint_acc(
        *(d_a0),
        ((((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else {
    const auto &[d_a0] = std::get<typename Uint::D9>(d.v());
    return Nat::of_uint_acc(
        *(d_a0),
        (((((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  }
}

__attribute__((pure)) unsigned int Nat::of_uint(const Uint &d) {
  return Nat::of_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int Nat::of_hex_uint_acc(const Uint0 &d,
                                                        unsigned int acc) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D10>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0), Nat::tail_mul(16u, acc));
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D11>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0), (Nat::tail_mul(16u, acc) + 1));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D12>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0), ((Nat::tail_mul(16u, acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D13>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0),
                                (((Nat::tail_mul(16u, acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D14>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0), ((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D15>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0), (((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D16>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0), ((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D17>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D18>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D19>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Da>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Db>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Dc>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Dd>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::De>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else {
    const auto &[d_a0] = std::get<typename Uint0::Df>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
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

__attribute__((pure)) unsigned int Nat::of_hex_uint(const Uint0 &d) {
  return Nat::of_hex_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int Nat::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[d_u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return Nat::of_uint(d_u);
  } else {
    const auto &[d_u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return Nat::of_hex_uint(d_u);
  }
}
