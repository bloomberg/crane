#ifndef INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE
#define INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE

#include <algorithm>
#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::shared_ptr<Uint> a0;
  };

  struct D1 {
    std::shared_ptr<Uint> a0;
  };

  struct D2 {
    std::shared_ptr<Uint> a0;
  };

  struct D3 {
    std::shared_ptr<Uint> a0;
  };

  struct D4 {
    std::shared_ptr<Uint> a0;
  };

  struct D5 {
    std::shared_ptr<Uint> a0;
  };

  struct D6 {
    std::shared_ptr<Uint> a0;
  };

  struct D7 {
    std::shared_ptr<Uint> a0;
  };

  struct D8 {
    std::shared_ptr<Uint> a0;
  };

  struct D9 {
    std::shared_ptr<Uint> a0;
  };

  using variant_t = std::variant<Nil, D0, D1, D2, D3, D4, D5, D6, D7, D8, D9>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Uint() {}

  explicit Uint(Nil _v) : v_(_v) {}

  explicit Uint(D0 _v) : v_(std::move(_v)) {}

  explicit Uint(D1 _v) : v_(std::move(_v)) {}

  explicit Uint(D2 _v) : v_(std::move(_v)) {}

  explicit Uint(D3 _v) : v_(std::move(_v)) {}

  explicit Uint(D4 _v) : v_(std::move(_v)) {}

  explicit Uint(D5 _v) : v_(std::move(_v)) {}

  explicit Uint(D6 _v) : v_(std::move(_v)) {}

  explicit Uint(D7 _v) : v_(std::move(_v)) {}

  explicit Uint(D8 _v) : v_(std::move(_v)) {}

  explicit Uint(D9 _v) : v_(std::move(_v)) {}

  static Uint nil() { return Uint(Nil{}); }

  static Uint d0(Uint a0) {
    return Uint(D0{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d1(Uint a0) {
    return Uint(D1{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d2(Uint a0) {
    return Uint(D2{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d3(Uint a0) {
    return Uint(D3{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d4(Uint a0) {
    return Uint(D4{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d5(Uint a0) {
    return Uint(D5{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d6(Uint a0) {
    return Uint(D6{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d7(Uint a0) {
    return Uint(D7{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d8(Uint a0) {
    return Uint(D8{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d9(Uint a0) {
    return Uint(D9{std::make_shared<Uint>(std::move(a0))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Uint0 {
  // TYPES
  struct Nil0 {};

  struct D10 {
    std::shared_ptr<Uint0> a0;
  };

  struct D11 {
    std::shared_ptr<Uint0> a0;
  };

  struct D12 {
    std::shared_ptr<Uint0> a0;
  };

  struct D13 {
    std::shared_ptr<Uint0> a0;
  };

  struct D14 {
    std::shared_ptr<Uint0> a0;
  };

  struct D15 {
    std::shared_ptr<Uint0> a0;
  };

  struct D16 {
    std::shared_ptr<Uint0> a0;
  };

  struct D17 {
    std::shared_ptr<Uint0> a0;
  };

  struct D18 {
    std::shared_ptr<Uint0> a0;
  };

  struct D19 {
    std::shared_ptr<Uint0> a0;
  };

  struct Da {
    std::shared_ptr<Uint0> a0;
  };

  struct Db {
    std::shared_ptr<Uint0> a0;
  };

  struct Dc {
    std::shared_ptr<Uint0> a0;
  };

  struct Dd {
    std::shared_ptr<Uint0> a0;
  };

  struct De {
    std::shared_ptr<Uint0> a0;
  };

  struct Df {
    std::shared_ptr<Uint0> a0;
  };

  using variant_t = std::variant<Nil0, D10, D11, D12, D13, D14, D15, D16, D17,
                                 D18, D19, Da, Db, Dc, Dd, De, Df>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Uint0() {}

  explicit Uint0(Nil0 _v) : v_(_v) {}

  explicit Uint0(D10 _v) : v_(std::move(_v)) {}

  explicit Uint0(D11 _v) : v_(std::move(_v)) {}

  explicit Uint0(D12 _v) : v_(std::move(_v)) {}

  explicit Uint0(D13 _v) : v_(std::move(_v)) {}

  explicit Uint0(D14 _v) : v_(std::move(_v)) {}

  explicit Uint0(D15 _v) : v_(std::move(_v)) {}

  explicit Uint0(D16 _v) : v_(std::move(_v)) {}

  explicit Uint0(D17 _v) : v_(std::move(_v)) {}

  explicit Uint0(D18 _v) : v_(std::move(_v)) {}

  explicit Uint0(D19 _v) : v_(std::move(_v)) {}

  explicit Uint0(Da _v) : v_(std::move(_v)) {}

  explicit Uint0(Db _v) : v_(std::move(_v)) {}

  explicit Uint0(Dc _v) : v_(std::move(_v)) {}

  explicit Uint0(Dd _v) : v_(std::move(_v)) {}

  explicit Uint0(De _v) : v_(std::move(_v)) {}

  explicit Uint0(Df _v) : v_(std::move(_v)) {}

  static Uint0 nil0() { return Uint0(Nil0{}); }

  static Uint0 d10(Uint0 a0) {
    return Uint0(D10{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d11(Uint0 a0) {
    return Uint0(D11{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d12(Uint0 a0) {
    return Uint0(D12{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d13(Uint0 a0) {
    return Uint0(D13{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d14(Uint0 a0) {
    return Uint0(D14{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d15(Uint0 a0) {
    return Uint0(D15{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d16(Uint0 a0) {
    return Uint0(D16{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d17(Uint0 a0) {
    return Uint0(D17{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d18(Uint0 a0) {
    return Uint0(D18{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d19(Uint0 a0) {
    return Uint0(D19{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 da(Uint0 a0) {
    return Uint0(Da{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 db(Uint0 a0) {
    return Uint0(Db{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 dc(Uint0 a0) {
    return Uint0(Dc{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 dd(Uint0 a0) {
    return Uint0(Dd{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 de(Uint0 a0) {
    return Uint0(De{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 df(Uint0 a0) {
    return Uint0(Df{std::make_shared<Uint0>(std::move(a0))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    Uint u;
  };

  struct UIntHexadecimal {
    Uint0 u;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Uint1() {}

  explicit Uint1(UIntDecimal _v) : v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : v_(std::move(_v)) {}

  static Uint1 uintdecimal(Uint u) { return Uint1(UIntDecimal{std::move(u)}); }

  static Uint1 uinthexadecimal(Uint0 u) {
    return Uint1(UIntHexadecimal{std::move(u)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Nat {
  static uint64_t tail_add(uint64_t n, uint64_t m);
  static uint64_t tail_addmul(uint64_t r, uint64_t n, uint64_t m);
  static uint64_t tail_mul(uint64_t n, uint64_t m);
  static uint64_t of_uint_acc(const Uint &d, uint64_t acc);
  static uint64_t of_uint(const Uint &d);
  static uint64_t of_hex_uint_acc(const Uint0 &d, uint64_t acc);
  static uint64_t of_hex_uint(const Uint0 &d);
  static uint64_t of_num_uint(const Uint1 &d);
};

struct HistoricalEventSafetyTraceCase {
  struct State {
    uint64_t reservoir_level_cm;
    uint64_t downstream_stage_cm;
    uint64_t gate_open_pct;

    // ACCESSORS
    State clone() const {
      return State{this->reservoir_level_cm, this->downstream_stage_cm,
                   this->gate_open_pct};
    }
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
    std::function<uint64_t(uint64_t)> reservoir_area_curve_cm2;
    uint64_t design_head_cm;
    uint64_t timestep_s;

    // ACCESSORS
    PlantConfig clone() const {
      return PlantConfig{this->max_reservoir_cm,
                         this->max_downstream_cm,
                         this->gate_capacity_cm,
                         this->forecast_error_pct,
                         this->gate_slew_pct,
                         this->max_stage_rise_cm,
                         this->reservoir_area_min_cm2,
                         this->reservoir_area_max_cm2,
                         this->reservoir_area_curve_cm2,
                         this->design_head_cm,
                         this->timestep_s};
    }
  };

  static bool is_safe_bool(const PlantConfig &pconf, const State &s);

  struct InflowRecord {
    uint64_t ir_timestep;
    uint64_t ir_inflow_cm;

    // ACCESSORS
    InflowRecord clone() const {
      return InflowRecord{this->ir_timestep, this->ir_inflow_cm};
    }
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

    // ACCESSORS
    TestResult clone() const {
      return TestResult{this->tr_event_name, this->tr_initial_safe,
                        this->tr_final_safe, this->tr_max_level,
                        this->tr_max_stage};
    }
  };

  template <typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F1 &, State &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F2 &, uint64_t &>
  static State step_hist(F0 &&inflow, F1 &&ctrl, F2 &&stage_fn,
                         const PlantConfig &pconf, const State &s, uint64_t t) {
    uint64_t out = std::min(
        (UINT64_C(100) ? (pconf.gate_capacity_cm * ctrl(s, t)) / UINT64_C(100)
                       : 0),
        (s.reservoir_level_cm + inflow(t)));
    uint64_t new_level = ((((s.reservoir_level_cm + inflow(t)) - out) >
                                   (s.reservoir_level_cm + inflow(t))
                               ? 0
                               : ((s.reservoir_level_cm + inflow(t)) - out)));
    uint64_t new_stage = stage_fn(out);
    return State{new_level, new_stage, ctrl(s, t)};
  }

  template <typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F1 &, State &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F2 &, uint64_t &>
  static std::pair<std::pair<State, uint64_t>, uint64_t>
  simulate_with_max(F0 &&inflow, F1 &&ctrl, F2 &&stage_fn,
                    const PlantConfig &pconf, uint64_t horizon, State s,
                    uint64_t max_level, uint64_t max_stage) {
    if (horizon <= 0) {
      return std::make_pair(std::make_pair(std::move(s), max_level), max_stage);
    } else {
      uint64_t k = horizon - 1;
      State s_ = step_hist(inflow, ctrl, stage_fn, pconf, std::move(s), k);
      return simulate_with_max(inflow, ctrl, stage_fn, pconf, k, s_,
                               std::max(max_level, s_.reservoir_level_cm),
                               std::max(max_stage, s_.downstream_stage_cm));
    }
  }

  template <typename F3, typename F4>
    requires std::is_invocable_r_v<uint64_t, F3 &, State &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F4 &, uint64_t &>
  static TestResult
  run_historical_test(const PlantConfig &pconf, List<InflowRecord> event,
                      uint64_t default_inflow, F3 &&ctrl, F4 &&stage_fn,
                      const State &initial_state, uint64_t horizon,
                      uint64_t event_id) {
    std::function<uint64_t(uint64_t)> inflow =
        [=](uint64_t _x0) mutable -> uint64_t {
      return event_to_inflow(event, default_inflow, _x0);
    };
    bool initial_safe = is_safe_bool(pconf, initial_state);
    auto _cs = simulate_with_max(inflow, ctrl, stage_fn, pconf, horizon,
                                 initial_state, UINT64_C(0), UINT64_C(0));
    const std::pair<State, uint64_t> &p = _cs.first;
    const uint64_t &max_stg = _cs.second;
    const State &final_state = p.first;
    const uint64_t &max_lev = p.second;
    bool final_safe = is_safe_bool(pconf, final_state);
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

    // ACCESSORS
    MonotoneRatingTable clone() const {
      return MonotoneRatingTable{this->mrt_table};
    }
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

    // ACCESSORS
    HistoricalScenarioBundle clone() const {
      return HistoricalScenarioBundle{
          this->hsb_hist_plant, this->hsb_hist_table, this->hsb_hist_initial,
          this->hsb_test_1983,  this->hsb_test_2011,  this->hsb_hoover_plant,
          this->hsb_hoover_test};
    }
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
  static uint64_t hoover_stage_sample(uint64_t _x0);
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
