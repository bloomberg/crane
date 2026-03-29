#include <historical_event_safety_trace.h>

#include <functional>
#include <memory>
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

__attribute__((pure)) unsigned int PeanoNat::max(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return std::move(m);
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return n;
    } else {
      unsigned int m_ = m - 1;
      return (PeanoNat::max(std::move(n_), std::move(m_)) + 1);
    }
  }
}

__attribute__((pure)) unsigned int PeanoNat::min(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return 0u;
    } else {
      unsigned int m_ = m - 1;
      return (PeanoNat::min(n_, m_) + 1);
    }
  }
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

__attribute__((pure)) bool HistoricalEventSafetyTraceCase::is_safe_bool(
    const std::shared_ptr<HistoricalEventSafetyTraceCase::PlantConfig> &pconf,
    const std::shared_ptr<HistoricalEventSafetyTraceCase::State> &s) {
  return (PeanoNat::leb(s->reservoir_level_cm, pconf->max_reservoir_cm) &&
          PeanoNat::leb(s->downstream_stage_cm, pconf->max_downstream_cm));
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::event_to_inflow(
    const std::shared_ptr<
        List<std::shared_ptr<HistoricalEventSafetyTraceCase::InflowRecord>>>
        &event,
    const unsigned int default_inflow, const unsigned int t) {
  return std::visit(
      Overloaded{
          [&](const typename List<std::shared_ptr<
                  HistoricalEventSafetyTraceCase::InflowRecord>>::Nil _args)
              -> unsigned int { return std::move(default_inflow); },
          [&](const typename List<std::shared_ptr<
                  HistoricalEventSafetyTraceCase::InflowRecord>>::Cons _args)
              -> unsigned int {
            if (PeanoNat::eqb(t, _args.d_a0->ir_timestep)) {
              return _args.d_a0->ir_inflow_cm;
            } else {
              return event_to_inflow(_args.d_a1, std::move(default_inflow), t);
            }
          }},
      event->v());
}

__attribute__((pure)) bool HistoricalEventSafetyTraceCase::test_passes(
    const std::shared_ptr<HistoricalEventSafetyTraceCase::TestResult> &result) {
  return (result->tr_initial_safe && result->tr_final_safe);
}

__attribute__((pure)) bool HistoricalEventSafetyTraceCase::all_tests_pass(
    const std::shared_ptr<
        List<std::shared_ptr<HistoricalEventSafetyTraceCase::TestResult>>>
        &results) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<HistoricalEventSafetyTraceCase::TestResult>>::Nil
                 _args) -> bool { return true; },
          [](const typename List<
              std::shared_ptr<HistoricalEventSafetyTraceCase::TestResult>>::Cons
                 _args) -> bool {
            return (test_passes(_args.d_a0) && all_tests_pass(_args.d_a1));
          }},
      results->v());
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::stage_from_table(
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &tbl,
    const unsigned int base_stage, const unsigned int out) {
  return std::visit(
      Overloaded{
          [&](const typename List<std::pair<unsigned int, unsigned int>>::Nil
                  _args) -> unsigned int { return std::move(base_stage); },
          [&](const typename List<std::pair<unsigned int, unsigned int>>::Cons
                  _args) -> unsigned int {
            unsigned int q = _args.d_a0.first;
            unsigned int s = _args.d_a0.second;
            unsigned int tail = stage_from_table(_args.d_a1, base_stage, out);
            if (PeanoNat::leb(out, q)) {
              return s;
            } else {
              return PeanoNat::max(s, std::move(tail));
            }
          }},
      tbl->v());
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hist_witness_stage(const unsigned int out) {
  return PeanoNat::div(out, 2u);
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hist_witness_ctrl(
    const std::shared_ptr<HistoricalEventSafetyTraceCase::State> &s,
    const unsigned int _x) {
  if (PeanoNat::leb(90u, s->reservoir_level_cm)) {
    return 100u;
  } else {
    return 50u;
  }
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hoover_controller(
    const std::shared_ptr<HistoricalEventSafetyTraceCase::State> &s,
    const unsigned int _x) {
  if (PeanoNat::leb(2000u, s->reservoir_level_cm)) {
    return 100u;
  } else {
    if (PeanoNat::leb(1900u, s->reservoir_level_cm)) {
      return 75u;
    } else {
      if (PeanoNat::leb(1800u, s->reservoir_level_cm)) {
        return 50u;
      } else {
        if (PeanoNat::leb(1700u, s->reservoir_level_cm)) {
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
    const unsigned int out) {
  return stage_from_table(hoover_rating_table->mrt_table, 20u, out);
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::historical_lookup_1983(const unsigned int t) {
  return event_to_inflow(flood_1983_inflows, 0u, t);
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::historical_lookup_2011(const unsigned int t) {
  return event_to_inflow(flood_2011_inflows, 0u, t);
}

__attribute__((pure)) bool
HistoricalEventSafetyTraceCase::witness_test_initial_safe_at(
    const unsigned int h) {
  return run_historical_test(hist_witness_plant, flood_1983_inflows, 0u,
                             hist_witness_ctrl, hist_witness_stage,
                             hist_witness_initial, h, 1983u)
      ->tr_initial_safe;
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::witness_test_peak_level_at(
    const unsigned int h) {
  return run_historical_test(hist_witness_plant, flood_2011_inflows, 0u,
                             hist_witness_ctrl, hist_witness_stage,
                             hist_witness_initial, h, 2011u)
      ->tr_max_level;
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hoover_controller_sample(
    const unsigned int level) {
  return hoover_controller(
      std::make_shared<HistoricalEventSafetyTraceCase::State>(
          State{std::move(level), 20u, 0u}),
      0u);
}

__attribute__((pure)) unsigned int
HistoricalEventSafetyTraceCase::hoover_stage_sample(const unsigned int _x0) {
  return hoover_stage_from_rating(_x0);
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
