#ifndef INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE
#define INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Nat {};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct HistoricalEventSafetyTraceCase {
  struct State {
    uint64_t reservoir_level_cm;
    uint64_t downstream_stage_cm;
    uint64_t gate_open_pct;
  };

  struct PlantConfig {
    uint64_t max_reservoir_cm;
    uint64_t max_downstream_cm;
    uint64_t gate_capacity_cm;
    uint64_t forecast_error_pct;
    uint64_t gate_slew_pct;
    uint64_t max_stage_rise_cm;
    uint64_t reservoir_area_min_cm2;
    uint64_t reservoir_area_max_cm2;
    crane::fn<uint64_t(uint64_t)> reservoir_area_curve_cm2;
    uint64_t design_head_cm;
    uint64_t timestep_s;
  };

  static bool is_safe_bool(const PlantConfig &pconf, const State &s);

  struct InflowRecord {
    uint64_t ir_timestep;
    uint64_t ir_inflow_cm;
  };

  using HistoricalEvent = List<InflowRecord>;
  static uint64_t event_to_inflow(const List<InflowRecord> &event,
                                  uint64_t default_inflow, uint64_t t);

  struct TestResult {
    uint64_t tr_event_name;
    bool tr_initial_safe;
    bool tr_final_safe;
    uint64_t tr_max_level;
    uint64_t tr_max_stage;
  };

  template <typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F1 &, const State &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F2 &, uint64_t &>
  static State step_hist(F0 &&inflow, F1 &&ctrl, F2 &&stage_fn,
                         const PlantConfig &pconf, const State &s, uint64_t t) {
    uint64_t out =
        std::min(((pconf.gate_capacity_cm * ctrl(s, t)) / UINT64_C(100)),
                 (s.reservoir_level_cm + inflow(t)));
    auto &&_once1 = (s.reservoir_level_cm + inflow(t));
    uint64_t new_level = (((_once1 - out) > _once1 ? 0 : (_once1 - out)));
    uint64_t new_stage = stage_fn(out);
    return State{new_level, new_stage, ctrl(s, t)};
  }

  template <typename F0, typename F1, typename F2>
  static std::pair<std::pair<State, uint64_t>, uint64_t>
  simulate_with_max(F0 &&inflow, F1 &&ctrl, F2 &&stage_fn,
                    const PlantConfig &pconf, uint64_t horizon, const State &s,
                    uint64_t max_level, uint64_t max_stage) {
    if (horizon <= 0) {
      return std::make_pair(std::make_pair(s, max_level), max_stage);
    } else {
      uint64_t k = horizon - 1;
      State s_ = step_hist(inflow, ctrl, stage_fn, pconf, s, k);
      return simulate_with_max(inflow, ctrl, stage_fn, pconf, k, s_,
                               std::max(max_level, s_.reservoir_level_cm),
                               std::max(max_stage, s_.downstream_stage_cm));
    }
  }

  template <typename F3, typename F4>
  static TestResult
  run_historical_test(const PlantConfig &pconf, List<InflowRecord> event,
                      uint64_t default_inflow, F3 &&ctrl, F4 &&stage_fn,
                      const State &initial_state, uint64_t horizon,
                      uint64_t event_id) {
    crane::fn<uint64_t(uint64_t)> inflow = [=](uint64_t _x0) -> uint64_t {
      return event_to_inflow(std::move(event), default_inflow, _x0);
    };
    bool initial_safe = is_safe_bool(pconf, initial_state);
    auto [p, max_stg] =
        simulate_with_max(inflow, ctrl, stage_fn, pconf, horizon, initial_state,
                          UINT64_C(0), UINT64_C(0));
    auto [final_state, max_lev] = std::move(p);
    bool final_safe = is_safe_bool(pconf, std::move(final_state));
    return TestResult{event_id, initial_safe, final_safe, max_lev, max_stg};
  }

  static bool test_passes(const TestResult &result);
  static bool all_tests_pass(const List<TestResult> &results);
  using RatingTable = List<std::pair<uint64_t, uint64_t>>;
  static uint64_t
  stage_from_table(const List<std::pair<uint64_t, uint64_t>> &tbl,
                   uint64_t base_stage, uint64_t out);

  struct MonotoneRatingTable {
    RatingTable mrt_table;
  };

  static inline const HistoricalEvent flood_1983_inflows =
      List<InflowRecord>::cons(
          InflowRecord{UINT64_C(0), UINT64_C(50)},
          List<InflowRecord>::cons(
              InflowRecord{UINT64_C(1), UINT64_C(75)},
              List<InflowRecord>::cons(
                  InflowRecord{UINT64_C(2), UINT64_C(100)},
                  List<InflowRecord>::cons(
                      InflowRecord{UINT64_C(3), UINT64_C(150)},
                      List<InflowRecord>::cons(
                          InflowRecord{UINT64_C(4), UINT64_C(200)},
                          List<InflowRecord>::cons(
                              InflowRecord{UINT64_C(5), UINT64_C(250)},
                              List<InflowRecord>::cons(
                                  InflowRecord{UINT64_C(6), UINT64_C(300)},
                                  List<InflowRecord>::cons(
                                      InflowRecord{UINT64_C(7), UINT64_C(250)},
                                      List<InflowRecord>::cons(
                                          InflowRecord{UINT64_C(8),
                                                       UINT64_C(200)},
                                          List<InflowRecord>::cons(
                                              InflowRecord{UINT64_C(9),
                                                           UINT64_C(150)},
                                              List<InflowRecord>::
                                                  nil()))))))))));
  static inline const HistoricalEvent flood_2011_inflows =
      List<InflowRecord>::cons(
          InflowRecord{UINT64_C(0), UINT64_C(100)},
          List<InflowRecord>::cons(
              InflowRecord{UINT64_C(1), UINT64_C(150)},
              List<InflowRecord>::cons(
                  InflowRecord{UINT64_C(2), UINT64_C(200)},
                  List<InflowRecord>::cons(
                      InflowRecord{UINT64_C(3), UINT64_C(300)},
                      List<InflowRecord>::cons(
                          InflowRecord{UINT64_C(4), UINT64_C(400)},
                          List<InflowRecord>::cons(
                              InflowRecord{UINT64_C(5), UINT64_C(350)},
                              List<InflowRecord>::cons(
                                  InflowRecord{UINT64_C(6), UINT64_C(300)},
                                  List<InflowRecord>::cons(
                                      InflowRecord{UINT64_C(7), UINT64_C(250)},
                                      List<InflowRecord>::cons(
                                          InflowRecord{UINT64_C(8),
                                                       UINT64_C(200)},
                                          List<InflowRecord>::cons(
                                              InflowRecord{UINT64_C(9),
                                                           UINT64_C(150)},
                                              List<InflowRecord>::
                                                  nil()))))))))));
  static inline const HistoricalEvent dual_peak_scenario =
      List<InflowRecord>::cons(
          InflowRecord{UINT64_C(0), UINT64_C(30)},
          List<InflowRecord>::cons(
              InflowRecord{UINT64_C(1), UINT64_C(60)},
              List<InflowRecord>::cons(
                  InflowRecord{UINT64_C(2), UINT64_C(120)},
                  List<InflowRecord>::cons(
                      InflowRecord{UINT64_C(3), UINT64_C(200)},
                      List<InflowRecord>::cons(
                          InflowRecord{UINT64_C(4), UINT64_C(300)},
                          List<InflowRecord>::cons(
                              InflowRecord{UINT64_C(5), UINT64_C(380)},
                              List<InflowRecord>::cons(
                                  InflowRecord{UINT64_C(6), UINT64_C(420)},
                                  List<InflowRecord>::cons(
                                      InflowRecord{UINT64_C(7), UINT64_C(400)},
                                      List<InflowRecord>::cons(
                                          InflowRecord{UINT64_C(8),
                                                       UINT64_C(350)},
                                          List<InflowRecord>::cons(
                                              InflowRecord{UINT64_C(9),
                                                           UINT64_C(280)},
                                              List<InflowRecord>::
                                                  nil()))))))))));
  static inline const PlantConfig hist_witness_plant = PlantConfig{
      UINT64_C(500), UINT64_C(500), UINT64_C(500),
      UINT64_C(1),   UINT64_C(5),   UINT64_C(10),
      UINT64_C(100), UINT64_C(100), [](uint64_t) {
return UINT64_C(100); },
      UINT64_C(100), UINT64_C(1)};
  static uint64_t hist_witness_stage(uint64_t out);
  static uint64_t hist_witness_ctrl(const State &s, uint64_t _x);
  static inline const State hist_witness_initial =
      State{UINT64_C(50), UINT64_C(0), UINT64_C(0)};
  static inline const TestResult hist_test_1983 = run_historical_test(
      hist_witness_plant, flood_1983_inflows, UINT64_C(0), hist_witness_ctrl,
      hist_witness_stage, hist_witness_initial, UINT64_C(10), UINT64_C(1983));
  static inline const TestResult hist_test_2011 = run_historical_test(
      hist_witness_plant, flood_2011_inflows, UINT64_C(0), hist_witness_ctrl,
      hist_witness_stage, hist_witness_initial, UINT64_C(10), UINT64_C(2011));
  static inline const PlantConfig hoover_dam_config = PlantConfig{
      UINT64_C(2200), UINT64_C(100),  UINT64_C(500),
      UINT64_C(15),   UINT64_C(5),    UINT64_C(10),
      UINT64_C(1000), UINT64_C(1000), [](uint64_t) {
return UINT64_C(1000); },
      UINT64_C(200),  UINT64_C(60)};
  static inline const State hoover_initial_state =
      State{UINT64_C(1500), UINT64_C(20), UINT64_C(0)};
  static uint64_t hoover_controller(const State &s, uint64_t _x);
  static inline const MonotoneRatingTable hoover_rating_table =
      MonotoneRatingTable{List<std::pair<uint64_t, uint64_t>>::cons(
          std::make_pair(UINT64_C(100), UINT64_C(30)),
          List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(UINT64_C(200), UINT64_C(45)),
              List<std::pair<uint64_t, uint64_t>>::cons(
                  std::make_pair(UINT64_C(300), UINT64_C(60)),
                  List<std::pair<uint64_t, uint64_t>>::cons(
                      std::make_pair(UINT64_C(400), UINT64_C(75)),
                      List<std::pair<uint64_t, uint64_t>>::cons(
                          std::make_pair(UINT64_C(500), UINT64_C(90)),
                          List<std::pair<uint64_t, uint64_t>>::nil())))))};
  static uint64_t hoover_stage_from_rating(uint64_t out);
  static inline const TestResult hoover_test =
      run_historical_test(hoover_dam_config, dual_peak_scenario, UINT64_C(0),
                          hoover_controller, hoover_stage_from_rating,
                          hoover_initial_state, UINT64_C(10), UINT64_C(9001));

  struct HistoricalScenarioBundle {
    PlantConfig hsb_hist_plant;
    MonotoneRatingTable hsb_hist_table;
    State hsb_hist_initial;
    TestResult hsb_test_1983;
    TestResult hsb_test_2011;
    PlantConfig hsb_hoover_plant;
    TestResult hsb_hoover_test;
  };

  static inline const HistoricalScenarioBundle historical_bundle =
      HistoricalScenarioBundle{hist_witness_plant,   hoover_rating_table,
                               hist_witness_initial, hist_test_1983,
                               hist_test_2011,       hoover_dam_config,
                               hoover_test};
  static uint64_t historical_lookup_1983(uint64_t t);
  static uint64_t historical_lookup_2011(uint64_t t);
  static bool witness_test_initial_safe_at(uint64_t h);
  static uint64_t witness_test_peak_level_at(uint64_t h);
  static uint64_t hoover_controller_sample(uint64_t level);
  static uint64_t hoover_stage_sample(uint64_t x0_);
  static inline const uint64_t sample_bundle_test_count =
      List<TestResult>::cons(
          historical_bundle.hsb_test_1983,
          List<TestResult>::cons(
              historical_bundle.hsb_test_2011,
              List<TestResult>::cons(historical_bundle.hsb_hoover_test,
                                     List<TestResult>::nil())))
          .length();
  static inline const bool sample_bundle_initial_safe =
      historical_bundle.hsb_test_1983.tr_initial_safe;
  static inline const uint64_t sample_bundle_hist_2011_id =
      historical_bundle.hsb_test_2011.tr_event_name;
  static inline const bool sample_all_tests_pass =
      all_tests_pass(List<TestResult>::cons(
          historical_bundle.hsb_test_1983,
          List<TestResult>::cons(
              historical_bundle.hsb_test_2011,
              List<TestResult>::cons(historical_bundle.hsb_hoover_test,
                                     List<TestResult>::nil()))));
};

#endif // INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE
