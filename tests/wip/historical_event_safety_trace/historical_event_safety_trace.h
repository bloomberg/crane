#ifndef INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE
#define INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     return (_args.d_a1->length() + 1);
                   }},
        this->v());
  }
};

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D1 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D2 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D3 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D4 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D5 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D6 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D7 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D8 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D9 {
    std::shared_ptr<Uint> d_a0;
  };

  using variant_t = std::variant<Nil, D0, D1, D2, D3, D4, D5, D6, D7, D8, D9>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Uint(Nil _v) : d_v_(std::move(_v)) {}

  explicit Uint(D0 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D1 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D2 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D3 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D4 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D5 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D6 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D7 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D8 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D9 _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Uint> Nil_() {
      return std::shared_ptr<Uint>(new Uint(Nil{}));
    }

    static std::shared_ptr<Uint> D0_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint>(new Uint(D0{a0}));
    }

    static std::shared_ptr<Uint> D1_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint>(new Uint(D1{a0}));
    }

    static std::shared_ptr<Uint> D2_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint>(new Uint(D2{a0}));
    }

    static std::shared_ptr<Uint> D3_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint>(new Uint(D3{a0}));
    }

    static std::shared_ptr<Uint> D4_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint>(new Uint(D4{a0}));
    }

    static std::shared_ptr<Uint> D5_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint>(new Uint(D5{a0}));
    }

    static std::shared_ptr<Uint> D6_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint>(new Uint(D6{a0}));
    }

    static std::shared_ptr<Uint> D7_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint>(new Uint(D7{a0}));
    }

    static std::shared_ptr<Uint> D8_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint>(new Uint(D8{a0}));
    }

    static std::shared_ptr<Uint> D9_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint>(new Uint(D9{a0}));
    }

    static std::unique_ptr<Uint> Nil_uptr() {
      return std::unique_ptr<Uint>(new Uint(Nil{}));
    }

    static std::unique_ptr<Uint> D0_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint>(new Uint(D0{a0}));
    }

    static std::unique_ptr<Uint> D1_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint>(new Uint(D1{a0}));
    }

    static std::unique_ptr<Uint> D2_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint>(new Uint(D2{a0}));
    }

    static std::unique_ptr<Uint> D3_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint>(new Uint(D3{a0}));
    }

    static std::unique_ptr<Uint> D4_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint>(new Uint(D4{a0}));
    }

    static std::unique_ptr<Uint> D5_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint>(new Uint(D5{a0}));
    }

    static std::unique_ptr<Uint> D6_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint>(new Uint(D6{a0}));
    }

    static std::unique_ptr<Uint> D7_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint>(new Uint(D7{a0}));
    }

    static std::unique_ptr<Uint> D8_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint>(new Uint(D8{a0}));
    }

    static std::unique_ptr<Uint> D9_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint>(new Uint(D9{a0}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Uint0 {
  // TYPES
  struct Nil0 {};

  struct D10 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D11 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D12 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D13 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D14 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D15 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D16 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D17 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D18 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D19 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Da {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Db {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Dc {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Dd {
    std::shared_ptr<Uint0> d_a0;
  };

  struct De {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Df {
    std::shared_ptr<Uint0> d_a0;
  };

  using variant_t = std::variant<Nil0, D10, D11, D12, D13, D14, D15, D16, D17,
                                 D18, D19, Da, Db, Dc, Dd, De, Df>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Uint0(Nil0 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D10 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D11 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D12 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D13 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D14 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D15 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D16 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D17 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D18 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D19 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Da _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Db _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Dc _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Dd _v) : d_v_(std::move(_v)) {}

  explicit Uint0(De _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Df _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Uint0> Nil0_() {
      return std::shared_ptr<Uint0>(new Uint0(Nil0{}));
    }

    static std::shared_ptr<Uint0> D10_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(D10{a0}));
    }

    static std::shared_ptr<Uint0> D11_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(D11{a0}));
    }

    static std::shared_ptr<Uint0> D12_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(D12{a0}));
    }

    static std::shared_ptr<Uint0> D13_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(D13{a0}));
    }

    static std::shared_ptr<Uint0> D14_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(D14{a0}));
    }

    static std::shared_ptr<Uint0> D15_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(D15{a0}));
    }

    static std::shared_ptr<Uint0> D16_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(D16{a0}));
    }

    static std::shared_ptr<Uint0> D17_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(D17{a0}));
    }

    static std::shared_ptr<Uint0> D18_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(D18{a0}));
    }

    static std::shared_ptr<Uint0> D19_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(D19{a0}));
    }

    static std::shared_ptr<Uint0> Da_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(Da{a0}));
    }

    static std::shared_ptr<Uint0> Db_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(Db{a0}));
    }

    static std::shared_ptr<Uint0> Dc_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(Dc{a0}));
    }

    static std::shared_ptr<Uint0> Dd_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(Dd{a0}));
    }

    static std::shared_ptr<Uint0> De_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(De{a0}));
    }

    static std::shared_ptr<Uint0> Df_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint0>(new Uint0(Df{a0}));
    }

    static std::unique_ptr<Uint0> Nil0_uptr() {
      return std::unique_ptr<Uint0>(new Uint0(Nil0{}));
    }

    static std::unique_ptr<Uint0> D10_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(D10{a0}));
    }

    static std::unique_ptr<Uint0> D11_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(D11{a0}));
    }

    static std::unique_ptr<Uint0> D12_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(D12{a0}));
    }

    static std::unique_ptr<Uint0> D13_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(D13{a0}));
    }

    static std::unique_ptr<Uint0> D14_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(D14{a0}));
    }

    static std::unique_ptr<Uint0> D15_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(D15{a0}));
    }

    static std::unique_ptr<Uint0> D16_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(D16{a0}));
    }

    static std::unique_ptr<Uint0> D17_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(D17{a0}));
    }

    static std::unique_ptr<Uint0> D18_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(D18{a0}));
    }

    static std::unique_ptr<Uint0> D19_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(D19{a0}));
    }

    static std::unique_ptr<Uint0> Da_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(Da{a0}));
    }

    static std::unique_ptr<Uint0> Db_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(Db{a0}));
    }

    static std::unique_ptr<Uint0> Dc_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(Dc{a0}));
    }

    static std::unique_ptr<Uint0> Dd_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(Dd{a0}));
    }

    static std::unique_ptr<Uint0> De_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(De{a0}));
    }

    static std::unique_ptr<Uint0> Df_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint0>(new Uint0(Df{a0}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct PeanoNat {
  __attribute__((pure)) static bool eqb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static bool leb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static unsigned int max(const unsigned int n,
                                                const unsigned int m);
  __attribute__((pure)) static unsigned int min(const unsigned int n,
                                                const unsigned int m);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    std::shared_ptr<Uint> d_a0;
  };

  struct UIntHexadecimal {
    std::shared_ptr<Uint0> d_a0;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Uint1(UIntDecimal _v) : d_v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Uint1>
    UIntDecimal_(const std::shared_ptr<Uint> &a0) {
      return std::shared_ptr<Uint1>(new Uint1(UIntDecimal{a0}));
    }

    static std::shared_ptr<Uint1>
    UIntHexadecimal_(const std::shared_ptr<Uint0> &a0) {
      return std::shared_ptr<Uint1>(new Uint1(UIntHexadecimal{a0}));
    }

    static std::unique_ptr<Uint1>
    UIntDecimal_uptr(const std::shared_ptr<Uint> &a0) {
      return std::unique_ptr<Uint1>(new Uint1(UIntDecimal{a0}));
    }

    static std::unique_ptr<Uint1>
    UIntHexadecimal_uptr(const std::shared_ptr<Uint0> &a0) {
      return std::unique_ptr<Uint1>(new Uint1(UIntHexadecimal{a0}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Nat {
  __attribute__((pure)) static unsigned int tail_add(const unsigned int n,
                                                     const unsigned int m);
  __attribute__((pure)) static unsigned int
  tail_addmul(const unsigned int r, const unsigned int n, const unsigned int m);
  __attribute__((pure)) static unsigned int tail_mul(const unsigned int n,
                                                     const unsigned int m);
  __attribute__((pure)) static unsigned int
  of_uint_acc(const std::shared_ptr<Uint> &d, const unsigned int acc);
  __attribute__((pure)) static unsigned int
  of_uint(const std::shared_ptr<Uint> &d);
  __attribute__((pure)) static unsigned int
  of_hex_uint_acc(const std::shared_ptr<Uint0> &d, const unsigned int acc);
  __attribute__((pure)) static unsigned int
  of_hex_uint(const std::shared_ptr<Uint0> &d);
  __attribute__((pure)) static unsigned int
  of_num_uint(const std::shared_ptr<Uint1> &d);
};

struct HistoricalEventSafetyTraceCase {
  struct State {
    unsigned int reservoir_level_cm;
    unsigned int downstream_stage_cm;
    unsigned int gate_open_pct;
  };

  struct PlantConfig {
    unsigned int max_reservoir_cm;
    unsigned int max_downstream_cm;
    unsigned int gate_capacity_cm;
    unsigned int forecast_error_pct;
    unsigned int gate_slew_pct;
    unsigned int max_stage_rise_cm;
    unsigned int reservoir_area_min_cm2;
    unsigned int reservoir_area_max_cm2;
    std::function<unsigned int(unsigned int)> reservoir_area_curve_cm2;
    unsigned int design_head_cm;
    unsigned int timestep_s;
  };

  __attribute__((pure)) static bool
  is_safe_bool(const std::shared_ptr<PlantConfig> &pconf,
               const std::shared_ptr<State> &s);

  struct InflowRecord {
    unsigned int ir_timestep;
    unsigned int ir_inflow_cm;
  };

  using HistoricalEvent = std::shared_ptr<List<std::shared_ptr<InflowRecord>>>;
  __attribute__((pure)) static unsigned int event_to_inflow(
      const std::shared_ptr<List<std::shared_ptr<InflowRecord>>> &event,
      const unsigned int default_inflow, const unsigned int t);

  struct TestResult {
    unsigned int tr_event_name;
    bool tr_initial_safe;
    bool tr_final_safe;
    unsigned int tr_max_level;
    unsigned int tr_max_stage;
  };

  template <MapsTo<unsigned int, unsigned int> F0,
            MapsTo<unsigned int, std::shared_ptr<State>, unsigned int> F1,
            MapsTo<unsigned int, unsigned int> F2>
  static std::shared_ptr<State>
  step_hist(F0 &&inflow, F1 &&ctrl, F2 &&stage_fn,
            const std::shared_ptr<PlantConfig> &pconf, std::shared_ptr<State> s,
            const unsigned int t) {
    unsigned int out = PeanoNat::min(
        PeanoNat::div((pconf->gate_capacity_cm * ctrl(s)(t)), 100u),
        (s->reservoir_level_cm + inflow(t)));
    unsigned int new_level =
        ((((s->reservoir_level_cm + inflow(t)) - out) >
                  (s->reservoir_level_cm + inflow(t))
              ? 0
              : ((s->reservoir_level_cm + inflow(t)) - out)));
    unsigned int new_stage = stage_fn(std::move(out));
    return std::make_shared<State>(State{std::move(new_level),
                                         std::move(new_stage),
                                         ctrl(std::move(s), std::move(t))});
  }

  template <MapsTo<unsigned int, unsigned int> F0,
            MapsTo<unsigned int, std::shared_ptr<State>, unsigned int> F1,
            MapsTo<unsigned int, unsigned int> F2>
  __attribute__((pure)) static std::pair<
      std::pair<std::shared_ptr<State>, unsigned int>, unsigned int>
  simulate_with_max(F0 &&inflow, F1 &&ctrl, F2 &&stage_fn,
                    const std::shared_ptr<PlantConfig> &pconf,
                    const unsigned int horizon, std::shared_ptr<State> s,
                    const unsigned int max_level,
                    const unsigned int max_stage) {
    if (horizon <= 0) {
      return std::make_pair(std::make_pair(std::move(s), std::move(max_level)),
                            std::move(max_stage));
    } else {
      unsigned int k = horizon - 1;
      std::shared_ptr<State> s_ =
          step_hist(inflow, ctrl, stage_fn, pconf, s, std::move(k));
      return simulate_with_max(
          inflow, ctrl, stage_fn, pconf, std::move(k), std::move(s_),
          PeanoNat::max(std::move(max_level),
                        std::move(s_)->reservoir_level_cm),
          PeanoNat::max(std::move(max_stage),
                        std::move(s_)->downstream_stage_cm));
    }
  }

  template <MapsTo<unsigned int, std::shared_ptr<State>, unsigned int> F3,
            MapsTo<unsigned int, unsigned int> F4>
  static std::shared_ptr<TestResult> run_historical_test(
      const std::shared_ptr<PlantConfig> &pconf,
      const std::shared_ptr<List<std::shared_ptr<InflowRecord>>> &event,
      const unsigned int default_inflow, F3 &&ctrl, F4 &&stage_fn,
      const std::shared_ptr<State> &initial_state, const unsigned int horizon,
      const unsigned int event_id) {
    std::function<unsigned int(unsigned int)> inflow =
        [&](unsigned int _x0) -> unsigned int {
      return event_to_inflow(event, default_inflow, _x0);
    };
    bool initial_safe = is_safe_bool(pconf, initial_state);
    std::pair<std::shared_ptr<State>, unsigned int> p =
        simulate_with_max(inflow, ctrl, stage_fn, pconf, horizon, initial_state,
                          0u, 0u)
            .first;
    unsigned int max_stg = simulate_with_max(inflow, ctrl, stage_fn, pconf,
                                             horizon, initial_state, 0u, 0u)
                               .second;
    std::shared_ptr<State> final_state = p.first;
    unsigned int max_lev = p.second;
    bool final_safe = is_safe_bool(pconf, final_state);
    return std::make_shared<TestResult>(
        TestResult{event_id, initial_safe, std::move(final_safe),
                   std::move(max_lev), std::move(max_stg)});
  }

  __attribute__((pure)) static bool
  test_passes(const std::shared_ptr<TestResult> &result);
  __attribute__((pure)) static bool all_tests_pass(
      const std::shared_ptr<List<std::shared_ptr<TestResult>>> &results);
  using RatingTable =
      std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>;
  __attribute__((pure)) static unsigned int stage_from_table(
      const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &tbl,
      const unsigned int base_stage, const unsigned int out);

  struct MonotoneRatingTable {
    RatingTable mrt_table;
  };

  static inline const HistoricalEvent flood_1983_inflows =
      List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
          std::make_shared<InflowRecord>(InflowRecord{0u, 50u}),
          List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
              std::make_shared<InflowRecord>(InflowRecord{1u, 75u}),
              List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                  std::make_shared<InflowRecord>(InflowRecord{2u, 100u}),
                  List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                      std::make_shared<InflowRecord>(InflowRecord{3u, 150u}),
                      List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                          std::make_shared<InflowRecord>(
                              InflowRecord{4u, 200u}),
                          List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                              std::make_shared<InflowRecord>(
                                  InflowRecord{5u, 250u}),
                              List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                                  std::make_shared<InflowRecord>(
                                      InflowRecord{6u, 300u}),
                                  List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                                      std::make_shared<InflowRecord>(
                                          InflowRecord{7u, 250u}),
                                      List<
                                          std::shared_ptr<InflowRecord>>::ctor::
                                          Cons_(
                                              std::make_shared<InflowRecord>(
                                                  InflowRecord{8u, 200u}),
                                              List<std::shared_ptr<
                                                  InflowRecord>>::ctor::
                                                  Cons_(
                                                      std::make_shared<
                                                          InflowRecord>(
                                                          InflowRecord{9u,
                                                                       150u}),
                                                      List<std::shared_ptr<
                                                          InflowRecord>>::ctor::
                                                          Nil_()))))))))));
  static inline const HistoricalEvent flood_2011_inflows =
      List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
          std::make_shared<InflowRecord>(InflowRecord{0u, 100u}),
          List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
              std::make_shared<InflowRecord>(InflowRecord{1u, 150u}),
              List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                  std::make_shared<InflowRecord>(InflowRecord{2u, 200u}),
                  List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                      std::make_shared<InflowRecord>(InflowRecord{3u, 300u}),
                      List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                          std::make_shared<InflowRecord>(
                              InflowRecord{4u, 400u}),
                          List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                              std::make_shared<InflowRecord>(
                                  InflowRecord{5u, 350u}),
                              List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                                  std::make_shared<InflowRecord>(
                                      InflowRecord{6u, 300u}),
                                  List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                                      std::make_shared<InflowRecord>(
                                          InflowRecord{7u, 250u}),
                                      List<
                                          std::shared_ptr<InflowRecord>>::ctor::
                                          Cons_(
                                              std::make_shared<InflowRecord>(
                                                  InflowRecord{8u, 200u}),
                                              List<std::shared_ptr<
                                                  InflowRecord>>::ctor::
                                                  Cons_(
                                                      std::make_shared<
                                                          InflowRecord>(
                                                          InflowRecord{9u,
                                                                       150u}),
                                                      List<std::shared_ptr<
                                                          InflowRecord>>::ctor::
                                                          Nil_()))))))))));
  static inline const HistoricalEvent dual_peak_scenario =
      List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
          std::make_shared<InflowRecord>(InflowRecord{0u, 30u}),
          List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
              std::make_shared<InflowRecord>(InflowRecord{1u, 60u}),
              List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                  std::make_shared<InflowRecord>(InflowRecord{2u, 120u}),
                  List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                      std::make_shared<InflowRecord>(InflowRecord{3u, 200u}),
                      List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                          std::make_shared<InflowRecord>(
                              InflowRecord{4u, 300u}),
                          List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                              std::make_shared<InflowRecord>(
                                  InflowRecord{5u, 380u}),
                              List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                                  std::make_shared<InflowRecord>(
                                      InflowRecord{6u, 420u}),
                                  List<std::shared_ptr<InflowRecord>>::ctor::Cons_(
                                      std::make_shared<InflowRecord>(
                                          InflowRecord{7u, 400u}),
                                      List<
                                          std::shared_ptr<InflowRecord>>::ctor::
                                          Cons_(
                                              std::make_shared<InflowRecord>(
                                                  InflowRecord{8u, 350u}),
                                              List<std::shared_ptr<
                                                  InflowRecord>>::ctor::
                                                  Cons_(
                                                      std::make_shared<
                                                          InflowRecord>(
                                                          InflowRecord{9u,
                                                                       280u}),
                                                      List<std::shared_ptr<
                                                          InflowRecord>>::ctor::
                                                          Nil_()))))))))));
  static inline const std::shared_ptr<PlantConfig> hist_witness_plant =
      std::make_shared<PlantConfig>(
          PlantConfig{500u, 500u, 500u, 1u, 5u, 10u, 100u, 100u,
                      [](unsigned int _x) { return 100u; }, 100u, 1u});
  __attribute__((pure)) static unsigned int
  hist_witness_stage(const unsigned int out);
  __attribute__((pure)) static unsigned int
  hist_witness_ctrl(const std::shared_ptr<State> &s, const unsigned int _x);
  static inline const std::shared_ptr<State> hist_witness_initial =
      std::make_shared<State>(State{50u, 0u, 0u});
  static inline const std::shared_ptr<TestResult> hist_test_1983 =
      run_historical_test(hist_witness_plant, flood_1983_inflows, 0u,
                          hist_witness_ctrl, hist_witness_stage,
                          hist_witness_initial, 10u, 1983u);
  static inline const std::shared_ptr<TestResult> hist_test_2011 =
      run_historical_test(hist_witness_plant, flood_2011_inflows, 0u,
                          hist_witness_ctrl, hist_witness_stage,
                          hist_witness_initial, 10u, 2011u);
  static inline const std::shared_ptr<PlantConfig> hoover_dam_config =
      std::make_shared<PlantConfig>(
          PlantConfig{2200u, 100u, 500u, 15u, 5u, 10u, 1000u, 1000u,
                      [](unsigned int _x) { return 1000u; }, 200u, 60u});
  static inline const std::shared_ptr<State> hoover_initial_state =
      std::make_shared<State>(State{1500u, 20u, 0u});
  __attribute__((pure)) static unsigned int
  hoover_controller(const std::shared_ptr<State> &s, const unsigned int _x);
  static inline const std::shared_ptr<MonotoneRatingTable> hoover_rating_table =
      std::make_shared<MonotoneRatingTable>(MonotoneRatingTable{
          List<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
              std::make_pair(100u, 30u),
              List<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
                  std::make_pair(200u, 45u),
                  List<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
                      std::make_pair(300u, 60u),
                      List<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
                          std::make_pair(400u, 75u),
                          List<std::pair<unsigned int, unsigned int>>::ctor::
                              Cons_(
                                  std::make_pair(500u, 90u),
                                  List<std::pair<unsigned int, unsigned int>>::
                                      ctor::Nil_())))))});
  __attribute__((pure)) static unsigned int
  hoover_stage_from_rating(const unsigned int out);
  static inline const std::shared_ptr<TestResult> hoover_test =
      run_historical_test(
          hoover_dam_config, dual_peak_scenario, 0u, hoover_controller,
          hoover_stage_from_rating, hoover_initial_state, 10u,
          Nat::of_num_uint(
              Uint1::ctor::UIntDecimal_(Uint::ctor::D9_(Uint::ctor::D0_(
                  Uint::ctor::D0_(Uint::ctor::D1_(Uint::ctor::Nil_())))))));

  struct HistoricalScenarioBundle {
    std::shared_ptr<PlantConfig> hsb_hist_plant;
    std::shared_ptr<MonotoneRatingTable> hsb_hist_table;
    std::shared_ptr<State> hsb_hist_initial;
    std::shared_ptr<TestResult> hsb_test_1983;
    std::shared_ptr<TestResult> hsb_test_2011;
    std::shared_ptr<PlantConfig> hsb_hoover_plant;
    std::shared_ptr<TestResult> hsb_hoover_test;
  };

  static inline const std::shared_ptr<HistoricalScenarioBundle>
      historical_bundle =
          std::make_shared<HistoricalScenarioBundle>(HistoricalScenarioBundle{
              hist_witness_plant, hoover_rating_table, hist_witness_initial,
              hist_test_1983, hist_test_2011, hoover_dam_config, hoover_test});
  __attribute__((pure)) static unsigned int
  historical_lookup_1983(const unsigned int t);
  __attribute__((pure)) static unsigned int
  historical_lookup_2011(const unsigned int t);
  __attribute__((pure)) static bool
  witness_test_initial_safe_at(const unsigned int h);
  __attribute__((pure)) static unsigned int
  witness_test_peak_level_at(const unsigned int h);
  __attribute__((pure)) static unsigned int
  hoover_controller_sample(const unsigned int level);
  __attribute__((pure)) static unsigned int
  hoover_stage_sample(const unsigned int _x0);
  static inline const unsigned int sample_bundle_test_count =
      List<std::shared_ptr<TestResult>>::ctor::Cons_(
          historical_bundle->hsb_test_1983,
          List<std::shared_ptr<TestResult>>::ctor::Cons_(
              historical_bundle->hsb_test_2011,
              List<std::shared_ptr<TestResult>>::ctor::Cons_(
                  historical_bundle->hsb_hoover_test,
                  List<std::shared_ptr<TestResult>>::ctor::Nil_())))
          ->length();
  static inline const bool sample_bundle_initial_safe =
      historical_bundle->hsb_test_1983->tr_initial_safe;
  static inline const unsigned int sample_bundle_hist_2011_id =
      historical_bundle->hsb_test_2011->tr_event_name;
  static inline const bool sample_all_tests_pass =
      all_tests_pass(List<std::shared_ptr<TestResult>>::ctor::Cons_(
          historical_bundle->hsb_test_1983,
          List<std::shared_ptr<TestResult>>::ctor::Cons_(
              historical_bundle->hsb_test_2011,
              List<std::shared_ptr<TestResult>>::ctor::Cons_(
                  historical_bundle->hsb_hoover_test,
                  List<std::shared_ptr<TestResult>>::ctor::Nil_()))));
};

#endif // INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE
