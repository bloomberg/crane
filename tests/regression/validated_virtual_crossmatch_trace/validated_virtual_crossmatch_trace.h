#ifndef INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE
#define INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE

#include <algorithm>
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
  __attribute__((pure)) bool existsb(F0 &&f) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return false;
    } else {
      const auto &_m = *std::get_if<typename List<t_A>::Cons>(&this->v());
      return (f(_m.d_a0) || _m.d_a1->existsb(f));
    }
  }

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &_m = *std::get_if<typename List<t_A>::Cons>(&this->v());
      return _m.d_a1->template fold_left<T1>(f, f(a0, _m.d_a0));
    }
  }

  template <typename T1, MapsTo<std::shared_ptr<List<T1>>, t_A> F0>
  std::shared_ptr<List<T1>> flat_map(F0 &&f) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &_m = *std::get_if<typename List<t_A>::Cons>(&this->v());
      return f(_m.d_a0)->app(_m.d_a1->template flat_map<T1>(f));
    }
  }

  __attribute__((pure)) unsigned int length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &_m = *std::get_if<typename List<t_A>::Cons>(&this->v());
      return (_m.d_a1->length() + 1);
    }
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &_m = *std::get_if<typename List<t_A>::Cons>(&this->v());
      return List<t_A>::cons(_m.d_a0, _m.d_a1->app(m));
    }
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

struct PeanoNat {
  __attribute__((pure)) static bool eq_dec(const unsigned int n,
                                           const unsigned int m);
};

struct Bool {
  __attribute__((pure)) static bool bool_dec(const bool b1, const bool b2);
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

struct ValidatedVirtualCrossmatchTraceCase {
  enum class HLALocus { e_LOCUS_A, e_LOCUS_B, e_LOCUS_DR };

  template <typename T1>
  static T1 HLALocus_rect(const T1 f, const T1 f0, const T1 f1,
                          const HLALocus h) {
    switch (h) {
    case HLALocus::e_LOCUS_A: {
      return f;
    }
    case HLALocus::e_LOCUS_B: {
      return f0;
    }
    case HLALocus::e_LOCUS_DR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 HLALocus_rec(const T1 f, const T1 f0, const T1 f1,
                         const HLALocus h) {
    switch (h) {
    case HLALocus::e_LOCUS_A: {
      return f;
    }
    case HLALocus::e_LOCUS_B: {
      return f0;
    }
    case HLALocus::e_LOCUS_DR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static bool hla_locus_eq_dec(const HLALocus x,
                                                     const HLALocus y);

  struct HLAAllele {
    HLALocus hla_locus;
    unsigned int hla_group;
  };

  __attribute__((pure)) static bool
  hla_allele_eq_dec(const std::shared_ptr<HLAAllele> &x,
                    const std::shared_ptr<HLAAllele> &y);
  __attribute__((pure)) static bool
  hla_allele_eqb(const std::shared_ptr<HLAAllele> &x,
                 const std::shared_ptr<HLAAllele> &y);

  struct HLATyping {
    std::shared_ptr<List<std::shared_ptr<HLAAllele>>> hla_typed_alleles;
  };

  struct HLAEpitope {
    unsigned int epitope_id;
    HLALocus epitope_locus;
    bool epitope_immunogenic;
  };

  __attribute__((pure)) static bool
  epitope_eq_dec(const std::shared_ptr<HLAEpitope> &x,
                 const std::shared_ptr<HLAEpitope> &y);
  __attribute__((pure)) static bool
  epitope_eqb(const std::shared_ptr<HLAEpitope> &x,
              const std::shared_ptr<HLAEpitope> &y);
  static inline const std::shared_ptr<HLAEpitope> eplet_62GE =
      std::make_shared<HLAEpitope>(HLAEpitope{62u, HLALocus::e_LOCUS_A, true});
  static inline const std::shared_ptr<HLAEpitope> eplet_65QIA =
      std::make_shared<HLAEpitope>(HLAEpitope{65u, HLALocus::e_LOCUS_A, true});
  static inline const std::shared_ptr<HLAEpitope> eplet_142T =
      std::make_shared<HLAEpitope>(HLAEpitope{142u, HLALocus::e_LOCUS_B, true});
  static inline const std::shared_ptr<HLAEpitope> eplet_77N =
      std::make_shared<HLAEpitope>(HLAEpitope{77u, HLALocus::e_LOCUS_DR, true});
  static std::shared_ptr<List<std::shared_ptr<HLAEpitope>>>
  allele_epitopes(const std::shared_ptr<HLAAllele> &a);
  static std::shared_ptr<List<std::shared_ptr<HLAEpitope>>>
  typing_epitopes(const std::shared_ptr<HLATyping> &t);
  static std::shared_ptr<List<std::shared_ptr<HLAEpitope>>>
  epitope_dedup(const std::shared_ptr<List<std::shared_ptr<HLAEpitope>>> &l);

  struct EpitopeAntibody {
    std::shared_ptr<HLAEpitope> ab_epitope;
    unsigned int ab_mfi;
    bool ab_complement_fixing;
  };

  struct VirtualXMProfile {
    std::shared_ptr<List<std::shared_ptr<EpitopeAntibody>>> vxm_epitope_abs;
    unsigned int vxm_current_pra;
    unsigned int vxm_peak_pra;
    unsigned int vxm_sensitization_events;
  };

  struct MFIThresholdConfig {
    unsigned int mfi_cfg_negative;
    unsigned int mfi_cfg_weak_positive;
    unsigned int mfi_cfg_moderate;
    unsigned int mfi_cfg_strong;
    unsigned int mfi_cfg_lab_id;
    bool mfi_cfg_validated;
  };

  __attribute__((pure)) static bool
  mfi_config_valid(const std::shared_ptr<MFIThresholdConfig> &cfg);
  static inline const std::shared_ptr<MFIThresholdConfig>
      example_luminex_thresholds = std::make_shared<MFIThresholdConfig>(
          MFIThresholdConfig{1000u, 3000u, 8000u, 12000u, 1u, true});

  struct ValidatedMFIConfig {
    std::shared_ptr<MFIThresholdConfig> vmc_config;
  };

  static inline const std::shared_ptr<ValidatedMFIConfig> validated_luminex =
      std::make_shared<ValidatedMFIConfig>(
          ValidatedMFIConfig{example_luminex_thresholds});
  enum class MFIStrength {
    e_MFI_NEGATIVE,
    e_MFI_WEAKPOSITIVE,
    e_MFI_MODERATE,
    e_MFI_STRONG,
    e_MFI_VERYSTRONG
  };

  template <typename T1>
  static T1 MFIStrength_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                             const T1 f3, const MFIStrength m) {
    switch (m) {
    case MFIStrength::e_MFI_NEGATIVE: {
      return f;
    }
    case MFIStrength::e_MFI_WEAKPOSITIVE: {
      return f0;
    }
    case MFIStrength::e_MFI_MODERATE: {
      return f1;
    }
    case MFIStrength::e_MFI_STRONG: {
      return f2;
    }
    case MFIStrength::e_MFI_VERYSTRONG: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 MFIStrength_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                            const T1 f3, const MFIStrength m) {
    switch (m) {
    case MFIStrength::e_MFI_NEGATIVE: {
      return f;
    }
    case MFIStrength::e_MFI_WEAKPOSITIVE: {
      return f0;
    }
    case MFIStrength::e_MFI_MODERATE: {
      return f1;
    }
    case MFIStrength::e_MFI_STRONG: {
      return f2;
    }
    case MFIStrength::e_MFI_VERYSTRONG: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static MFIStrength
  classify_mfi_with_config(const std::shared_ptr<MFIThresholdConfig> &cfg,
                           const unsigned int mfi);
  __attribute__((pure)) static MFIStrength
  classify_mfi_safe(const std::shared_ptr<ValidatedMFIConfig> &vcfg,
                    const unsigned int mfi);
  static inline const unsigned int mfi_negative_threshold = 1000u;
  __attribute__((pure)) static unsigned int
  max_dsa_mfi(const std::shared_ptr<VirtualXMProfile> &recipient,
              const std::shared_ptr<HLATyping> &donor);
  __attribute__((pure)) static bool
  has_complement_fixing_dsa(const std::shared_ptr<VirtualXMProfile> &recipient,
                            const std::shared_ptr<HLATyping> &donor);
  enum class VirtualXMResult {
    e_VXM_NEGATIVE,
    e_VXM_WEAKPOSITIVE,
    e_VXM_POSITIVE,
    e_VXM_STRONGPOSITIVE
  };

  template <typename T1>
  static T1 VirtualXMResult_rect(const T1 f, const T1 f0, const T1 f1,
                                 const T1 f2, const VirtualXMResult v) {
    switch (v) {
    case VirtualXMResult::e_VXM_NEGATIVE: {
      return f;
    }
    case VirtualXMResult::e_VXM_WEAKPOSITIVE: {
      return f0;
    }
    case VirtualXMResult::e_VXM_POSITIVE: {
      return f1;
    }
    case VirtualXMResult::e_VXM_STRONGPOSITIVE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 VirtualXMResult_rec(const T1 f, const T1 f0, const T1 f1,
                                const T1 f2, const VirtualXMResult v) {
    switch (v) {
    case VirtualXMResult::e_VXM_NEGATIVE: {
      return f;
    }
    case VirtualXMResult::e_VXM_WEAKPOSITIVE: {
      return f0;
    }
    case VirtualXMResult::e_VXM_POSITIVE: {
      return f1;
    }
    case VirtualXMResult::e_VXM_STRONGPOSITIVE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static VirtualXMResult
  virtual_crossmatch_safe(const std::shared_ptr<ValidatedMFIConfig> &vcfg,
                          const std::shared_ptr<VirtualXMProfile> &recipient,
                          const std::shared_ptr<HLATyping> &donor);
  enum class TransplantAcceptability {
    e_ACCEPTABLE,
    e_ACCEPTABLE_WITH_DESENSITIZATION,
    e_UNACCEPTABLE_HIGH_RISK,
    e_ABSOLUTE_CONTRAINDICATION
  };

  template <typename T1>
  static T1 TransplantAcceptability_rect(const T1 f, const T1 f0, const T1 f1,
                                         const T1 f2,
                                         const TransplantAcceptability t) {
    switch (t) {
    case TransplantAcceptability::e_ACCEPTABLE: {
      return f;
    }
    case TransplantAcceptability::e_ACCEPTABLE_WITH_DESENSITIZATION: {
      return f0;
    }
    case TransplantAcceptability::e_UNACCEPTABLE_HIGH_RISK: {
      return f1;
    }
    case TransplantAcceptability::e_ABSOLUTE_CONTRAINDICATION: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TransplantAcceptability_rec(const T1 f, const T1 f0, const T1 f1,
                                        const T1 f2,
                                        const TransplantAcceptability t) {
    switch (t) {
    case TransplantAcceptability::e_ACCEPTABLE: {
      return f;
    }
    case TransplantAcceptability::e_ACCEPTABLE_WITH_DESENSITIZATION: {
      return f0;
    }
    case TransplantAcceptability::e_UNACCEPTABLE_HIGH_RISK: {
      return f1;
    }
    case TransplantAcceptability::e_ABSOLUTE_CONTRAINDICATION: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static TransplantAcceptability
  transplant_acceptability(const VirtualXMResult vxm,
                           const bool complement_fixing_dsa);
  __attribute__((pure)) static TransplantAcceptability
  full_virtual_crossmatch_safe(
      const std::shared_ptr<ValidatedMFIConfig> &vcfg,
      const std::shared_ptr<VirtualXMProfile> &recipient,
      const std::shared_ptr<HLATyping> &donor);
  enum class TestConfidence {
    e_CONFIDENCE_HIGH,
    e_CONFIDENCE_MEDIUM,
    e_CONFIDENCE_LOW
  };

  template <typename T1>
  static T1 TestConfidence_rect(const T1 f, const T1 f0, const T1 f1,
                                const TestConfidence t) {
    switch (t) {
    case TestConfidence::e_CONFIDENCE_HIGH: {
      return f;
    }
    case TestConfidence::e_CONFIDENCE_MEDIUM: {
      return f0;
    }
    case TestConfidence::e_CONFIDENCE_LOW: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TestConfidence_rec(const T1 f, const T1 f0, const T1 f1,
                               const TestConfidence t) {
    switch (t) {
    case TestConfidence::e_CONFIDENCE_HIGH: {
      return f;
    }
    case TestConfidence::e_CONFIDENCE_MEDIUM: {
      return f0;
    }
    case TestConfidence::e_CONFIDENCE_LOW: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }
  enum class CrossmatchResult {
    e_XM_COMPATIBLE,
    e_XM_INCOMPATIBLE,
    e_XM_INCONCLUSIVE,
    e_XM_NOT_DONE
  };

  template <typename T1>
  static T1 CrossmatchResult_rect(const T1 f, const T1 f0, const T1 f1,
                                  const T1 f2, const CrossmatchResult c) {
    switch (c) {
    case CrossmatchResult::e_XM_COMPATIBLE: {
      return f;
    }
    case CrossmatchResult::e_XM_INCOMPATIBLE: {
      return f0;
    }
    case CrossmatchResult::e_XM_INCONCLUSIVE: {
      return f1;
    }
    case CrossmatchResult::e_XM_NOT_DONE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 CrossmatchResult_rec(const T1 f, const T1 f0, const T1 f1,
                                 const T1 f2, const CrossmatchResult c) {
    switch (c) {
    case CrossmatchResult::e_XM_COMPATIBLE: {
      return f;
    }
    case CrossmatchResult::e_XM_INCOMPATIBLE: {
      return f0;
    }
    case CrossmatchResult::e_XM_INCONCLUSIVE: {
      return f1;
    }
    case CrossmatchResult::e_XM_NOT_DONE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  struct CrossmatchWithUncertainty {
    CrossmatchResult xmu_result;
    unsigned int xmu_method;
    TestConfidence xmu_confidence;
  };

  __attribute__((pure)) static bool
  safe_to_release(const std::shared_ptr<CrossmatchWithUncertainty> &xm);

  struct SafeTransfusionOrder {
    unsigned int sto_recipient_id;
    unsigned int sto_product_id;
    bool sto_compatibility_check;
    std::shared_ptr<CrossmatchWithUncertainty> sto_crossmatch;
    unsigned int sto_sample_collection_time;
    unsigned int sto_authorized_by;
    bool sto_emergency_release;
  };

  __attribute__((pure)) static bool
  order_sample_valid(const unsigned int collection_time,
                     const unsigned int current_time);
  __attribute__((pure)) static bool transfusion_order_authorized(
      const std::shared_ptr<SafeTransfusionOrder> &order,
      const unsigned int current_time);
  __attribute__((
      pure)) static std::optional<std::shared_ptr<SafeTransfusionOrder>>
  create_safe_transfusion_order(
      const unsigned int recipient_id, const unsigned int product_id,
      const bool compat_result, std::shared_ptr<CrossmatchWithUncertainty> xm,
      const unsigned int sample_time, const unsigned int current_time,
      const unsigned int authorizer, const bool is_emergency);
  static inline const std::shared_ptr<HLATyping> donor_hla = std::make_shared<
      HLATyping>(HLATyping{List<std::shared_ptr<HLAAllele>>::cons(
      std::make_shared<HLAAllele>(HLAAllele{HLALocus::e_LOCUS_A, 2u}),
      List<std::shared_ptr<HLAAllele>>::cons(
          std::make_shared<HLAAllele>(HLAAllele{HLALocus::e_LOCUS_A, 3u}),
          List<std::shared_ptr<HLAAllele>>::cons(
              std::make_shared<HLAAllele>(HLAAllele{HLALocus::e_LOCUS_B, 7u}),
              List<std::shared_ptr<HLAAllele>>::cons(
                  std::make_shared<HLAAllele>(
                      HLAAllele{HLALocus::e_LOCUS_DR, 4u}),
                  List<std::shared_ptr<HLAAllele>>::nil()))))});
  static inline const std::shared_ptr<VirtualXMProfile> weak_profile =
      std::make_shared<VirtualXMProfile>(VirtualXMProfile{
          List<std::shared_ptr<EpitopeAntibody>>::cons(
              std::make_shared<EpitopeAntibody>(
                  EpitopeAntibody{eplet_65QIA, 2500u, false}),
              List<std::shared_ptr<EpitopeAntibody>>::cons(
                  std::make_shared<EpitopeAntibody>(
                      EpitopeAntibody{eplet_77N, 800u, false}),
                  List<std::shared_ptr<EpitopeAntibody>>::nil())),
          32u, 40u, 2u});
  static inline const std::shared_ptr<VirtualXMProfile> strong_profile =
      std::make_shared<VirtualXMProfile>(VirtualXMProfile{
          List<std::shared_ptr<EpitopeAntibody>>::cons(
              std::make_shared<EpitopeAntibody>(
                  EpitopeAntibody{eplet_65QIA, 9000u, true}),
              List<std::shared_ptr<EpitopeAntibody>>::cons(
                  std::make_shared<EpitopeAntibody>(
                      EpitopeAntibody{eplet_142T, 6000u, false}),
                  List<std::shared_ptr<EpitopeAntibody>>::nil())),
          95u, 98u, 5u});
  static inline const std::shared_ptr<CrossmatchWithUncertainty>
      good_crossmatch = std::make_shared<CrossmatchWithUncertainty>(
          CrossmatchWithUncertainty{CrossmatchResult::e_XM_COMPATIBLE, 1u,
                                    TestConfidence::e_CONFIDENCE_HIGH});
  static inline const std::shared_ptr<CrossmatchWithUncertainty>
      bad_crossmatch = std::make_shared<CrossmatchWithUncertainty>(
          CrossmatchWithUncertainty{CrossmatchResult::e_XM_INCOMPATIBLE, 1u,
                                    TestConfidence::e_CONFIDENCE_HIGH});
  __attribute__((pure)) static bool
  risk_acceptable(const TransplantAcceptability a);
  static inline const bool sample_virtual_zero_negative = []() {
    switch (classify_mfi_safe(validated_luminex, 0u)) {
    case MFIStrength::e_MFI_NEGATIVE: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const unsigned int sample_dedup_count =
      epitope_dedup(typing_epitopes(donor_hla))->length();
  static inline const bool sample_weak_acceptability = []() {
    switch (full_virtual_crossmatch_safe(validated_luminex, weak_profile,
                                         donor_hla)) {
    case TransplantAcceptability::e_ACCEPTABLE_WITH_DESENSITIZATION: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const bool sample_strong_absolute_contra = []() {
    switch (full_virtual_crossmatch_safe(validated_luminex, strong_profile,
                                         donor_hla)) {
    case TransplantAcceptability::e_ABSOLUTE_CONTRAINDICATION: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const bool sample_strong_has_complement_fixing_dsa =
      has_complement_fixing_dsa(strong_profile, donor_hla);
  static inline const unsigned int sample_strong_max_mfi =
      max_dsa_mfi(strong_profile, donor_hla);
  static inline const unsigned int sample_lab_id =
      validated_luminex->vmc_config->mfi_cfg_lab_id;
  static inline const bool sample_order_created = []() -> bool {
    auto _cs = create_safe_transfusion_order(
        100u, 200u,
        risk_acceptable(full_virtual_crossmatch_safe(validated_luminex,
                                                     weak_profile, donor_hla)),
        good_crossmatch, 0u, 1000u, 77u, false);
    if (_cs.has_value()) {
      const std::shared_ptr<SafeTransfusionOrder> &_x = *_cs;
      return true;
    } else {
      return false;
    }
  }();
  static inline const bool sample_order_blocked = []() -> bool {
    auto _cs = create_safe_transfusion_order(
        100u, 201u,
        risk_acceptable(full_virtual_crossmatch_safe(
            validated_luminex, strong_profile, donor_hla)),
        bad_crossmatch, 0u, 1000u, 77u, false);
    if (_cs.has_value()) {
      const std::shared_ptr<SafeTransfusionOrder> &_x = *_cs;
      return false;
    } else {
      return true;
    }
  }();
  static inline const bool sample_authorized_order_stays_authorized =
      []() -> bool {
    auto _cs = create_safe_transfusion_order(100u, 202u, true, good_crossmatch,
                                             100u, 200u, 88u, false);
    if (_cs.has_value()) {
      const std::shared_ptr<SafeTransfusionOrder> &order = *_cs;
      return transfusion_order_authorized(order, 200u);
    } else {
      return false;
    }
  }();
};

#endif // INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE
