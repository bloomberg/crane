#ifndef INCLUDED_VALIDATED_PUMP_DELIVERY_TRACE
#define INCLUDED_VALIDATED_PUMP_DELIVERY_TRACE

#include <memory>
#include <optional>
#include <type_traits>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool forallb(F0 &&f) const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil &) -> bool { return true; },
                   [&](const typename List<t_A>::Cons &_args) -> bool {
                     return (f(_args.d_a0) && _args.d_a1->forallb(f));
                   }},
        this->v());
  }

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil &) -> T1 { return a0; },
                   [&](const typename List<t_A>::Cons &_args) -> T1 {
                     return _args.d_a1->template fold_left<T1>(
                         f, f(a0, _args.d_a0));
                   }},
        this->v());
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil &) -> unsigned int { return 0u; },
            [](const typename List<t_A>::Cons &_args) -> unsigned int {
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

public:
  // CREATORS
  explicit Uint(Nil _v) : d_v_(_v) {}

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

  static std::shared_ptr<Uint> nil() { return std::make_shared<Uint>(Nil{}); }

  static std::shared_ptr<Uint> d0(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D0{a0});
  }

  static std::shared_ptr<Uint> d0(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D0{std::move(a0)});
  }

  static std::shared_ptr<Uint> d1(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D1{a0});
  }

  static std::shared_ptr<Uint> d1(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D1{std::move(a0)});
  }

  static std::shared_ptr<Uint> d2(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D2{a0});
  }

  static std::shared_ptr<Uint> d2(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D2{std::move(a0)});
  }

  static std::shared_ptr<Uint> d3(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D3{a0});
  }

  static std::shared_ptr<Uint> d3(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D3{std::move(a0)});
  }

  static std::shared_ptr<Uint> d4(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D4{a0});
  }

  static std::shared_ptr<Uint> d4(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D4{std::move(a0)});
  }

  static std::shared_ptr<Uint> d5(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D5{a0});
  }

  static std::shared_ptr<Uint> d5(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D5{std::move(a0)});
  }

  static std::shared_ptr<Uint> d6(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D6{a0});
  }

  static std::shared_ptr<Uint> d6(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D6{std::move(a0)});
  }

  static std::shared_ptr<Uint> d7(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D7{a0});
  }

  static std::shared_ptr<Uint> d7(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D7{std::move(a0)});
  }

  static std::shared_ptr<Uint> d8(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D8{a0});
  }

  static std::shared_ptr<Uint> d8(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D8{std::move(a0)});
  }

  static std::shared_ptr<Uint> d9(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D9{a0});
  }

  static std::shared_ptr<Uint> d9(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D9{std::move(a0)});
  }

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

public:
  // CREATORS
  explicit Uint0(Nil0 _v) : d_v_(_v) {}

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

  static std::shared_ptr<Uint0> nil0() {
    return std::make_shared<Uint0>(Nil0{});
  }

  static std::shared_ptr<Uint0> d10(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D10{a0});
  }

  static std::shared_ptr<Uint0> d10(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D10{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d11(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D11{a0});
  }

  static std::shared_ptr<Uint0> d11(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D11{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d12(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D12{a0});
  }

  static std::shared_ptr<Uint0> d12(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D12{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d13(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D13{a0});
  }

  static std::shared_ptr<Uint0> d13(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D13{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d14(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D14{a0});
  }

  static std::shared_ptr<Uint0> d14(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D14{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d15(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D15{a0});
  }

  static std::shared_ptr<Uint0> d15(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D15{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d16(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D16{a0});
  }

  static std::shared_ptr<Uint0> d16(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D16{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d17(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D17{a0});
  }

  static std::shared_ptr<Uint0> d17(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D17{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d18(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D18{a0});
  }

  static std::shared_ptr<Uint0> d18(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D18{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d19(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D19{a0});
  }

  static std::shared_ptr<Uint0> d19(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D19{std::move(a0)});
  }

  static std::shared_ptr<Uint0> da(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Da{a0});
  }

  static std::shared_ptr<Uint0> da(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Da{std::move(a0)});
  }

  static std::shared_ptr<Uint0> db(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Db{a0});
  }

  static std::shared_ptr<Uint0> db(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Db{std::move(a0)});
  }

  static std::shared_ptr<Uint0> dc(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Dc{a0});
  }

  static std::shared_ptr<Uint0> dc(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Dc{std::move(a0)});
  }

  static std::shared_ptr<Uint0> dd(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Dd{a0});
  }

  static std::shared_ptr<Uint0> dd(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Dd{std::move(a0)});
  }

  static std::shared_ptr<Uint0> de(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(De{a0});
  }

  static std::shared_ptr<Uint0> de(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(De{std::move(a0)});
  }

  static std::shared_ptr<Uint0> df(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Df{a0});
  }

  static std::shared_ptr<Uint0> df(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Df{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    std::shared_ptr<Uint> d_u;
  };

  struct UIntHexadecimal {
    std::shared_ptr<Uint0> d_u;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Uint1(UIntDecimal _v) : d_v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Uint1> uintdecimal(const std::shared_ptr<Uint> &u) {
    return std::make_shared<Uint1>(UIntDecimal{u});
  }

  static std::shared_ptr<Uint1> uintdecimal(std::shared_ptr<Uint> &&u) {
    return std::make_shared<Uint1>(UIntDecimal{std::move(u)});
  }

  static std::shared_ptr<Uint1>
  uinthexadecimal(const std::shared_ptr<Uint0> &u) {
    return std::make_shared<Uint1>(UIntHexadecimal{u});
  }

  static std::shared_ptr<Uint1> uinthexadecimal(std::shared_ptr<Uint0> &&u) {
    return std::make_shared<Uint1>(UIntHexadecimal{std::move(u)});
  }

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

struct ValidatedPumpDeliveryTraceCase {
  struct Mg_dL {
    unsigned int mg_dL_val;
  };

  struct Grams {
    unsigned int grams_val;
  };

  using Carbs_g = std::shared_ptr<Grams>;
  using Minutes = unsigned int;
  using DIA_minutes = unsigned int;
  using Insulin_twentieth = unsigned int;
  static inline const unsigned int ONE_UNIT = 20u;
  static inline const unsigned int BG_LEVEL2_HYPO = 54u;
  static inline const unsigned int BG_HYPO = 70u;
  static inline const unsigned int BG_HYPER = 180u;
  static inline const unsigned int BG_METER_MIN = 20u;
  static inline const unsigned int BG_METER_MAX = 600u;
  static inline const unsigned int CARBS_SANITY_MAX = 200u;
  __attribute__((pure)) static bool
  bg_in_meter_range(const std::shared_ptr<Mg_dL> &bg);
  __attribute__((pure)) static bool
  carbs_reasonable(const std::shared_ptr<Grams> &carbs);

  struct Config {
    unsigned int cfg_bg_rise_per_gram;
    unsigned int cfg_conservative_cob_absorption_percent;
    unsigned int cfg_suspend_threshold_mg_dl;
    unsigned int cfg_stacking_warning_threshold_min;
    unsigned int cfg_iob_high_threshold_twentieths;
  };

  static inline const std::shared_ptr<Config> default_config =
      std::make_shared<Config>(Config{4u, 30u, 80u, 60u, 200u});
  enum class ActivityState {
    e_ACTIVITY_NORMAL,
    e_ACTIVITY_LIGHTEXERCISE,
    e_ACTIVITY_MODERATEEXERCISE,
    e_ACTIVITY_INTENSEEXERCISE,
    e_ACTIVITY_ILLNESS,
    e_ACTIVITY_STRESS
  };

  template <typename T1>
  static T1 ActivityState_rect(const T1 f, const T1 f0, const T1 f1,
                               const T1 f2, const T1 f3, const T1 f4,
                               const ActivityState a) {
    switch (a) {
    case ActivityState::e_ACTIVITY_NORMAL: {
      return f;
    }
    case ActivityState::e_ACTIVITY_LIGHTEXERCISE: {
      return f0;
    }
    case ActivityState::e_ACTIVITY_MODERATEEXERCISE: {
      return f1;
    }
    case ActivityState::e_ACTIVITY_INTENSEEXERCISE: {
      return f2;
    }
    case ActivityState::e_ACTIVITY_ILLNESS: {
      return f3;
    }
    case ActivityState::e_ACTIVITY_STRESS: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 ActivityState_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                              const T1 f3, const T1 f4, const ActivityState a) {
    switch (a) {
    case ActivityState::e_ACTIVITY_NORMAL: {
      return f;
    }
    case ActivityState::e_ACTIVITY_LIGHTEXERCISE: {
      return f0;
    }
    case ActivityState::e_ACTIVITY_MODERATEEXERCISE: {
      return f1;
    }
    case ActivityState::e_ACTIVITY_INTENSEEXERCISE: {
      return f2;
    }
    case ActivityState::e_ACTIVITY_ILLNESS: {
      return f3;
    }
    case ActivityState::e_ACTIVITY_STRESS: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int
  isf_activity_modifier(const ActivityState state);
  __attribute__((pure)) static unsigned int
  icr_activity_modifier(const ActivityState state);

  struct FaultStatus {
    // TYPES
    struct Fault_None {};

    struct Fault_Occlusion {};

    struct Fault_LowReservoir {
      unsigned int d_a0;
    };

    struct Fault_BatteryLow {};

    struct Fault_Unknown {};

    using variant_t =
        std::variant<Fault_None, Fault_Occlusion, Fault_LowReservoir,
                     Fault_BatteryLow, Fault_Unknown>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit FaultStatus(Fault_None _v) : d_v_(_v) {}

    explicit FaultStatus(Fault_Occlusion _v) : d_v_(_v) {}

    explicit FaultStatus(Fault_LowReservoir _v) : d_v_(std::move(_v)) {}

    explicit FaultStatus(Fault_BatteryLow _v) : d_v_(_v) {}

    explicit FaultStatus(Fault_Unknown _v) : d_v_(_v) {}

    static std::shared_ptr<FaultStatus> fault_none() {
      return std::make_shared<FaultStatus>(Fault_None{});
    }

    static std::shared_ptr<FaultStatus> fault_occlusion() {
      return std::make_shared<FaultStatus>(Fault_Occlusion{});
    }

    static std::shared_ptr<FaultStatus> fault_lowreservoir(unsigned int a0) {
      return std::make_shared<FaultStatus>(Fault_LowReservoir{std::move(a0)});
    }

    static std::shared_ptr<FaultStatus> fault_batterylow() {
      return std::make_shared<FaultStatus>(Fault_BatteryLow{});
    }

    static std::shared_ptr<FaultStatus> fault_unknown() {
      return std::make_shared<FaultStatus>(Fault_Unknown{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool fault_blocks_bolus() const {
      return std::visit(
          Overloaded{[](const typename FaultStatus::Fault_None &) -> bool {
                       return false;
                     },
                     [](const typename FaultStatus::Fault_LowReservoir &_args)
                         -> bool { return _args.d_a0 < 10u; },
                     [](const typename FaultStatus::Fault_BatteryLow &)
                         -> bool { return false; },
                     [](const auto &) -> bool { return true; }},
          this->v());
    }
  };

  template <typename T1, MapsTo<T1, unsigned int> F2>
  static T1 FaultStatus_rect(const T1 f, const T1 f0, F2 &&f1, const T1 f2,
                             const T1 f3,
                             const std::shared_ptr<FaultStatus> &f4) {
    return std::visit(
        Overloaded{
            [&](const typename FaultStatus::Fault_None &) -> T1 { return f; },
            [&](const typename FaultStatus::Fault_Occlusion &) -> T1 {
              return f0;
            },
            [&](const typename FaultStatus::Fault_LowReservoir &_args) -> T1 {
              return f1(_args.d_a0);
            },
            [&](const typename FaultStatus::Fault_BatteryLow &) -> T1 {
              return f2;
            },
            [&](const typename FaultStatus::Fault_Unknown &) -> T1 {
              return f3;
            }},
        f4->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F2>
  static T1 FaultStatus_rec(const T1 f, const T1 f0, F2 &&f1, const T1 f2,
                            const T1 f3,
                            const std::shared_ptr<FaultStatus> &f4) {
    return std::visit(
        Overloaded{
            [&](const typename FaultStatus::Fault_None &) -> T1 { return f; },
            [&](const typename FaultStatus::Fault_Occlusion &) -> T1 {
              return f0;
            },
            [&](const typename FaultStatus::Fault_LowReservoir &_args) -> T1 {
              return f1(_args.d_a0);
            },
            [&](const typename FaultStatus::Fault_BatteryLow &) -> T1 {
              return f2;
            },
            [&](const typename FaultStatus::Fault_Unknown &) -> T1 {
              return f3;
            }},
        f4->v());
  }
  enum class InsulinType {
    e_INSULIN_HUMALOG,
    e_INSULIN_ASPART,
    e_INSULIN_LISPRO
  };

  template <typename T1>
  static T1 InsulinType_rect(const T1 f, const T1 f0, const T1 f1,
                             const InsulinType i) {
    switch (i) {
    case InsulinType::e_INSULIN_HUMALOG: {
      return f;
    }
    case InsulinType::e_INSULIN_ASPART: {
      return f0;
    }
    case InsulinType::e_INSULIN_LISPRO: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 InsulinType_rec(const T1 f, const T1 f0, const T1 f1,
                            const InsulinType i) {
    switch (i) {
    case InsulinType::e_INSULIN_HUMALOG: {
      return f;
    }
    case InsulinType::e_INSULIN_ASPART: {
      return f0;
    }
    case InsulinType::e_INSULIN_LISPRO: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static Minutes peak_time(const InsulinType itype,
                                                 const unsigned int _x);

  struct BolusEvent {
    unsigned int be_dose_twentieths;
    Minutes be_time_minutes;
  };

  __attribute__((pure)) static unsigned int div_ceil(const unsigned int a,
                                                     const unsigned int b);
  __attribute__((pure)) static bool
  event_time_valid(const unsigned int now,
                   const std::shared_ptr<BolusEvent> &event);
  __attribute__((pure)) static bool history_times_valid(
      const unsigned int now,
      const std::shared_ptr<List<std::shared_ptr<BolusEvent>>> &events);
  __attribute__((pure)) static bool history_sorted_from(
      const unsigned int prev,
      const std::shared_ptr<List<std::shared_ptr<BolusEvent>>> &events);
  __attribute__((pure)) static bool history_sorted_desc(
      const std::shared_ptr<List<std::shared_ptr<BolusEvent>>> &events);
  __attribute__((pure)) static bool history_valid(
      const unsigned int now,
      const std::shared_ptr<List<std::shared_ptr<BolusEvent>>> &events);
  __attribute__((pure)) static unsigned int
  bilinear_iob_fraction(const unsigned int elapsed, const unsigned int dia,
                        const InsulinType itype);
  __attribute__((pure)) static Insulin_twentieth
  bilinear_iob_from_bolus(const unsigned int now,
                          const std::shared_ptr<BolusEvent> &event,
                          const unsigned int dia, const InsulinType itype);
  __attribute__((pure)) static Insulin_twentieth total_bilinear_iob(
      const unsigned int now,
      const std::shared_ptr<List<std::shared_ptr<BolusEvent>>> &events,
      const unsigned int dia, const InsulinType itype);
  static std::shared_ptr<Mg_dL>
  apply_sensor_margin(std::shared_ptr<Mg_dL> bg,
                      const std::shared_ptr<Mg_dL> &target);
  __attribute__((pure)) static unsigned int
  adjusted_isf_tenths(const std::shared_ptr<Mg_dL> &bg,
                      const unsigned int base_isf_tenths);
  __attribute__((pure)) static Insulin_twentieth
  correction_twentieths_full(const unsigned int _x,
                             const std::shared_ptr<Mg_dL> &current_bg,
                             const std::shared_ptr<Mg_dL> &target_bg,
                             const unsigned int base_isf_tenths);
  __attribute__((pure)) static Insulin_twentieth
  apply_reverse_correction_twentieths(const unsigned int carb,
                                      const std::shared_ptr<Mg_dL> &current_bg,
                                      const std::shared_ptr<Mg_dL> &target_bg,
                                      const unsigned int isf_tenths);

  struct SuspendDecision {
    // TYPES
    struct Suspend_None {};

    struct Suspend_Reduce {
      Insulin_twentieth d_a0;
    };

    struct Suspend_Withhold {};

    using variant_t =
        std::variant<Suspend_None, Suspend_Reduce, Suspend_Withhold>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit SuspendDecision(Suspend_None _v) : d_v_(_v) {}

    explicit SuspendDecision(Suspend_Reduce _v) : d_v_(std::move(_v)) {}

    explicit SuspendDecision(Suspend_Withhold _v) : d_v_(_v) {}

    static std::shared_ptr<SuspendDecision> suspend_none() {
      return std::make_shared<SuspendDecision>(Suspend_None{});
    }

    static std::shared_ptr<SuspendDecision>
    suspend_reduce(Insulin_twentieth a0) {
      return std::make_shared<SuspendDecision>(Suspend_Reduce{std::move(a0)});
    }

    static std::shared_ptr<SuspendDecision> suspend_withhold() {
      return std::make_shared<SuspendDecision>(Suspend_Withhold{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 SuspendDecision_rect(const T1 f, F1 &&f0, const T1 f1,
                                 const std::shared_ptr<SuspendDecision> &s) {
    return std::visit(
        Overloaded{
            [&](const typename SuspendDecision::Suspend_None &) -> T1 {
              return f;
            },
            [&](const typename SuspendDecision::Suspend_Reduce &_args) -> T1 {
              return f0(_args.d_a0);
            },
            [&](const typename SuspendDecision::Suspend_Withhold &) -> T1 {
              return f1;
            }},
        s->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 SuspendDecision_rec(const T1 f, F1 &&f0, const T1 f1,
                                const std::shared_ptr<SuspendDecision> &s) {
    return std::visit(
        Overloaded{
            [&](const typename SuspendDecision::Suspend_None &) -> T1 {
              return f;
            },
            [&](const typename SuspendDecision::Suspend_Reduce &_args) -> T1 {
              return f0(_args.d_a0);
            },
            [&](const typename SuspendDecision::Suspend_Withhold &) -> T1 {
              return f1;
            }},
        s->v());
  }

  __attribute__((pure)) static unsigned int
  predict_bg_drop_tenths(const unsigned int iob_twentieths,
                         const unsigned int isf_tenths);
  __attribute__((pure)) static unsigned int
  conservative_cob_rise(const std::shared_ptr<Config> &cfg,
                        const unsigned int cob_grams);
  __attribute__((pure)) static unsigned int
  predicted_eventual_bg_tenths(const std::shared_ptr<Config> &cfg,
                               const std::shared_ptr<Mg_dL> &current_bg,
                               const unsigned int iob_twentieths,
                               const unsigned int cob_grams,
                               const unsigned int isf_tenths);
  static std::shared_ptr<SuspendDecision> suspend_check_tenths_with_cob(
      const std::shared_ptr<Config> &cfg,
      const std::shared_ptr<Mg_dL> &current_bg,
      const unsigned int iob_twentieths, const unsigned int cob_grams,
      const unsigned int isf_tenths, const unsigned int proposed);
  __attribute__((pure)) static Insulin_twentieth
  apply_suspend(const unsigned int proposed,
                const std::shared_ptr<SuspendDecision> &decision);
  __attribute__((pure)) static Insulin_twentieth
  pediatric_max_twentieths(const unsigned int weight_kg);
  __attribute__((pure)) static Insulin_twentieth
  cap_pediatric(const unsigned int bolus, const unsigned int weight_kg);

  struct PrecisionParams {
    unsigned int prec_icr_tenths;
    unsigned int prec_isf_tenths;
    std::shared_ptr<Mg_dL> prec_target_bg;
    DIA_minutes prec_dia;
    InsulinType prec_insulin_type;
  };

  __attribute__((pure)) static bool
  prec_params_valid(const std::shared_ptr<PrecisionParams> &p);

  struct PrecisionInput {
    Carbs_g pi_carbs_g;
    std::shared_ptr<Mg_dL> pi_current_bg;
    Minutes pi_now;
    std::shared_ptr<List<std::shared_ptr<BolusEvent>>> pi_bolus_history;
    ActivityState pi_activity;
    bool pi_use_sensor_margin;
    std::shared_ptr<FaultStatus> pi_fault;
    std::optional<unsigned int> pi_weight_kg;
  };

  __attribute__((pure)) static Insulin_twentieth
  carb_bolus_twentieths(const unsigned int carbs_g,
                        const unsigned int icr_tenths);
  __attribute__((pure)) static Insulin_twentieth
  calculate_precision_bolus(const std::shared_ptr<PrecisionInput> &input,
                            const std::shared_ptr<PrecisionParams> &params);
  __attribute__((pure)) static bool time_reasonable(const unsigned int now);
  __attribute__((pure)) static bool history_extraction_safe(
      const std::shared_ptr<List<std::shared_ptr<BolusEvent>>> &events);
  __attribute__((pure)) static unsigned int
  iob_high_threshold(const std::shared_ptr<Config> &cfg);
  __attribute__((pure)) static bool
  iob_dangerously_high(const unsigned int iob);

  struct PrecisionResult {
    // TYPES
    struct PrecOK {
      Insulin_twentieth d_a0;
      bool d_a1;
    };

    struct PrecError {
      unsigned int d_a0;
    };

    using variant_t = std::variant<PrecOK, PrecError>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit PrecisionResult(PrecOK _v) : d_v_(std::move(_v)) {}

    explicit PrecisionResult(PrecError _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<PrecisionResult> precok(Insulin_twentieth a0,
                                                   bool a1) {
      return std::make_shared<PrecisionResult>(
          PrecOK{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<PrecisionResult> precerror(unsigned int a0) {
      return std::make_shared<PrecisionResult>(PrecError{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool result_modified() const {
      return std::visit(
          Overloaded{[](const typename PrecisionResult::PrecOK &_args) -> bool {
                       return _args.d_a1;
                     },
                     [](const typename PrecisionResult::PrecError &) -> bool {
                       return false;
                     }},
          this->v());
    }

    __attribute__((pure)) unsigned int precision_result_code() const {
      return std::visit(
          Overloaded{[](const typename PrecisionResult::PrecOK &)
                         -> unsigned int { return 0u; },
                     [](const typename PrecisionResult::PrecError &_args)
                         -> unsigned int { return _args.d_a0; }},
          this->v());
    }
  };

  template <typename T1, MapsTo<T1, unsigned int, bool> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 PrecisionResult_rect(F0 &&f, F1 &&f0,
                                 const std::shared_ptr<PrecisionResult> &p) {
    return std::visit(
        Overloaded{[&](const typename PrecisionResult::PrecOK &_args) -> T1 {
                     return f(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename PrecisionResult::PrecError &_args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        p->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, bool> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 PrecisionResult_rec(F0 &&f, F1 &&f0,
                                const std::shared_ptr<PrecisionResult> &p) {
    return std::visit(
        Overloaded{[&](const typename PrecisionResult::PrecOK &_args) -> T1 {
                     return f(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename PrecisionResult::PrecError &_args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        p->v());
  }

  static inline const unsigned int prec_error_invalid_params = 1u;
  static inline const unsigned int prec_error_invalid_input = 2u;
  static inline const unsigned int prec_error_hypo = 3u;
  static inline const unsigned int prec_error_invalid_history = 4u;
  static inline const unsigned int prec_error_invalid_time = 5u;
  static inline const unsigned int prec_error_stacking = 6u;
  static inline const unsigned int prec_error_fault = 7u;
  static inline const unsigned int prec_error_tdd_exceeded = 8u;
  static inline const unsigned int prec_error_iob_high = 9u;
  static inline const unsigned int prec_error_extraction_unsafe = 10u;
  __attribute__((pure)) static bool bolus_too_soon(
      const unsigned int now,
      const std::shared_ptr<List<std::shared_ptr<BolusEvent>>> &history);
  __attribute__((pure)) static Insulin_twentieth
  cap_twentieths(const unsigned int t);
  static std::shared_ptr<PrecisionResult>
  validated_precision_bolus(std::shared_ptr<PrecisionInput> input,
                            const std::shared_ptr<PrecisionParams> &params);
  __attribute__((pure)) static std::optional<Insulin_twentieth>
  prec_result_twentieths(const std::shared_ptr<PrecisionResult> &r);

  struct MmolPrecisionInput {
    Carbs_g mpi_carbs_g;
    unsigned int mpi_current_bg_mmol_tenths;
    Minutes mpi_now;
    std::shared_ptr<List<std::shared_ptr<BolusEvent>>> mpi_bolus_history;
    ActivityState mpi_activity;
    bool mpi_use_sensor_margin;
    std::shared_ptr<FaultStatus> mpi_fault;
    std::optional<unsigned int> mpi_weight_kg;
  };

  __attribute__((pure)) static unsigned int
  mmol_tenths_to_mg_dL(const unsigned int mmol_tenths);
  static std::shared_ptr<PrecisionInput>
  convert_mmol_input(const std::shared_ptr<MmolPrecisionInput> &input);
  static std::shared_ptr<PrecisionResult>
  validated_mmol_bolus(const std::shared_ptr<MmolPrecisionInput> &input,
                       const std::shared_ptr<PrecisionParams> &params);
  enum class RoundingMode {
    e_ROUNDTWENTIETH,
    e_ROUNDTENTH,
    e_ROUNDHALF,
    e_ROUNDUNIT
  };

  template <typename T1>
  static T1 RoundingMode_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                              const RoundingMode r) {
    switch (r) {
    case RoundingMode::e_ROUNDTWENTIETH: {
      return f;
    }
    case RoundingMode::e_ROUNDTENTH: {
      return f0;
    }
    case RoundingMode::e_ROUNDHALF: {
      return f1;
    }
    case RoundingMode::e_ROUNDUNIT: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 RoundingMode_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                             const RoundingMode r) {
    switch (r) {
    case RoundingMode::e_ROUNDTWENTIETH: {
      return f;
    }
    case RoundingMode::e_ROUNDTENTH: {
      return f0;
    }
    case RoundingMode::e_ROUNDHALF: {
      return f1;
    }
    case RoundingMode::e_ROUNDUNIT: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int
  round_down_to_increment(const unsigned int t, const unsigned int increment);
  __attribute__((pure)) static Insulin_twentieth
  apply_rounding(const RoundingMode mode, const unsigned int t);
  __attribute__((pure)) static std::optional<Insulin_twentieth>
  final_delivery(const RoundingMode mode,
                 const std::shared_ptr<PrecisionResult> &result);

  struct PumpState {
    unsigned int ps_reservoir_twentieths;
    unsigned int ps_basal_rate_hundredths;
    Minutes ps_last_bolus_time;
    bool ps_occlusion_detected;
    unsigned int ps_battery_percent;
  };

  __attribute__((pure)) static bool
  pump_can_deliver(const std::shared_ptr<PumpState> &state,
                   const unsigned int dose);
  __attribute__((pure)) static unsigned int
  reservoir_after_bolus(const std::shared_ptr<PumpState> &state,
                        const unsigned int dose);
  __attribute__((pure)) static unsigned int
  option_nat_default(const std::optional<unsigned int> x, const unsigned int d);
  __attribute__((pure)) static bool
  pump_accepts_result(const std::shared_ptr<PumpState> &pump,
                      const RoundingMode mode,
                      const std::shared_ptr<PrecisionResult> &r);
  __attribute__((pure)) static unsigned int
  pump_reservoir_after_result(const std::shared_ptr<PumpState> &pump,
                              const RoundingMode mode,
                              const std::shared_ptr<PrecisionResult> &r);
  static inline const std::shared_ptr<PrecisionParams> witness_prec_params =
      std::make_shared<PrecisionParams>(
          PrecisionParams{100u, 500u, std::make_shared<Mg_dL>(Mg_dL{100u}),
                          240u, InsulinType::e_INSULIN_HUMALOG});
  static inline const std::shared_ptr<PrecisionInput> standard_input =
      std::make_shared<PrecisionInput>(PrecisionInput{
          std::make_shared<Grams>(Grams{60u}),
          std::make_shared<Mg_dL>(Mg_dL{150u}), 0u,
          List<std::shared_ptr<BolusEvent>>::nil(),
          ActivityState::e_ACTIVITY_NORMAL, false, FaultStatus::fault_none(),
          std::optional<unsigned int>()});
  static inline const std::shared_ptr<MmolPrecisionInput> mmol_input =
      std::make_shared<MmolPrecisionInput>(MmolPrecisionInput{
          std::make_shared<Grams>(Grams{60u}), 83u, 0u,
          List<std::shared_ptr<BolusEvent>>::nil(),
          ActivityState::e_ACTIVITY_NORMAL, false, FaultStatus::fault_none(),
          std::optional<unsigned int>()});
  static inline const std::shared_ptr<PrecisionInput> high_iob_input =
      std::make_shared<PrecisionInput>(PrecisionInput{
          std::make_shared<Grams>(Grams{0u}),
          std::make_shared<Mg_dL>(Mg_dL{150u}), 100u,
          List<std::shared_ptr<BolusEvent>>::cons(
              std::make_shared<BolusEvent>(BolusEvent{120u, 85u}),
              List<std::shared_ptr<BolusEvent>>::cons(
                  std::make_shared<BolusEvent>(BolusEvent{100u, 80u}),
                  List<std::shared_ptr<BolusEvent>>::nil())),
          ActivityState::e_ACTIVITY_NORMAL, false, FaultStatus::fault_none(),
          std::optional<unsigned int>()});
  static inline const std::shared_ptr<PrecisionInput> tdd_exceeded_input =
      std::make_shared<PrecisionInput>(PrecisionInput{
          std::make_shared<Grams>(Grams{60u}),
          std::make_shared<Mg_dL>(Mg_dL{150u}), 2000u,
          List<std::shared_ptr<BolusEvent>>::cons(
              std::make_shared<BolusEvent>(BolusEvent{500u, 1800u}),
              List<std::shared_ptr<BolusEvent>>::cons(
                  std::make_shared<BolusEvent>(BolusEvent{500u, 1500u}),
                  List<std::shared_ptr<BolusEvent>>::cons(
                      std::make_shared<BolusEvent>(BolusEvent{500u, 1000u}),
                      List<std::shared_ptr<BolusEvent>>::nil()))),
          ActivityState::e_ACTIVITY_NORMAL, false, FaultStatus::fault_none(),
          std::make_optional<unsigned int>(70u)});
  static inline const std::shared_ptr<PrecisionInput> occlusion_input =
      std::make_shared<PrecisionInput>(PrecisionInput{
          std::make_shared<Grams>(Grams{60u}),
          std::make_shared<Mg_dL>(Mg_dL{150u}), 120u,
          List<std::shared_ptr<BolusEvent>>::cons(
              std::make_shared<BolusEvent>(BolusEvent{40u, 100u}),
              List<std::shared_ptr<BolusEvent>>::nil()),
          ActivityState::e_ACTIVITY_NORMAL, false,
          FaultStatus::fault_occlusion(), std::optional<unsigned int>()});
  static inline const std::shared_ptr<PrecisionInput> battery_low_input =
      std::make_shared<PrecisionInput>(PrecisionInput{
          std::make_shared<Grams>(Grams{60u}),
          std::make_shared<Mg_dL>(Mg_dL{150u}), 120u,
          List<std::shared_ptr<BolusEvent>>::cons(
              std::make_shared<BolusEvent>(BolusEvent{40u, 100u}),
              List<std::shared_ptr<BolusEvent>>::nil()),
          ActivityState::e_ACTIVITY_NORMAL, false,
          FaultStatus::fault_batterylow(), std::optional<unsigned int>()});
  static inline const std::shared_ptr<PrecisionInput> pediatric_capped_input =
      std::make_shared<PrecisionInput>(PrecisionInput{
          std::make_shared<Grams>(Grams{200u}),
          std::make_shared<Mg_dL>(Mg_dL{400u}), 0u,
          List<std::shared_ptr<BolusEvent>>::nil(),
          ActivityState::e_ACTIVITY_NORMAL, false, FaultStatus::fault_none(),
          std::make_optional<unsigned int>(20u)});
  static inline const std::shared_ptr<PumpState> standard_pump =
      std::make_shared<PumpState>(PumpState{2000u, 100u, 0u, false, 80u});
  static inline const std::shared_ptr<PumpState> low_battery_pump =
      std::make_shared<PumpState>(PumpState{2000u, 100u, 0u, false, 4u});
  static inline const std::shared_ptr<PrecisionResult> standard_result =
      validated_precision_bolus(standard_input, witness_prec_params);
  static inline const std::shared_ptr<PrecisionResult> mmol_result =
      validated_mmol_bolus(mmol_input, witness_prec_params);
  static inline const std::shared_ptr<PrecisionResult> battery_low_result =
      validated_precision_bolus(battery_low_input, witness_prec_params);
  static inline const std::shared_ptr<PrecisionResult> pediatric_result =
      validated_precision_bolus(pediatric_capped_input, witness_prec_params);
  static inline const unsigned int standard_result_code =
      standard_result->precision_result_code();
  static inline const bool standard_modified =
      standard_result->result_modified();
  static inline const unsigned int standard_final_delivery_half =
      option_nat_default(
          final_delivery(RoundingMode::e_ROUNDHALF, standard_result), 0u);
  static inline const bool standard_pump_accepts = pump_accepts_result(
      standard_pump, RoundingMode::e_ROUNDHALF, standard_result);
  static inline const unsigned int standard_reservoir_after =
      pump_reservoir_after_result(standard_pump, RoundingMode::e_ROUNDHALF,
                                  standard_result);
  static inline const unsigned int mmol_result_code =
      mmol_result->precision_result_code();
  static inline const unsigned int mmol_final_delivery_tenth =
      option_nat_default(
          final_delivery(RoundingMode::e_ROUNDTENTH, mmol_result), 0u);
  static inline const unsigned int high_iob_error_code =
      validated_precision_bolus(high_iob_input, witness_prec_params)
          ->precision_result_code();
  static inline const unsigned int tdd_error_code =
      validated_precision_bolus(tdd_exceeded_input, witness_prec_params)
          ->precision_result_code();
  static inline const unsigned int occlusion_error_code =
      validated_precision_bolus(occlusion_input, witness_prec_params)
          ->precision_result_code();
  static inline const unsigned int battery_low_result_code =
      battery_low_result->precision_result_code();
  static inline const bool battery_low_pump_denied = !(pump_accepts_result(
      low_battery_pump, RoundingMode::e_ROUNDHALF, battery_low_result));
  static inline const unsigned int pediatric_result_code =
      pediatric_result->precision_result_code();
  static inline const bool pediatric_modified =
      pediatric_result->result_modified();
  static inline const unsigned int pediatric_final_delivery =
      option_nat_default(
          final_delivery(RoundingMode::e_ROUNDTWENTIETH, pediatric_result), 0u);
  static inline const bool low_reservoir_blocks =
      FaultStatus::fault_lowreservoir(5u)->fault_blocks_bolus();
  static inline const bool unknown_fault_blocks =
      FaultStatus::fault_unknown()->fault_blocks_bolus();
};

#endif // INCLUDED_VALIDATED_PUMP_DELIVERY_TRACE
