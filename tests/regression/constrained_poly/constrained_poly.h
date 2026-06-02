#ifndef INCLUDED_CONSTRAINED_POLY
#define INCLUDED_CONSTRAINED_POLY

#include <any>
#include <type_traits>
#include <utility>
#include <variant>

struct ConstrainedPoly {
  template <typename T1> static T1 poly_id(T1 x) { return x; }

  template <typename A, typename B> struct UPair {
    A ufst;
    B usnd;
  };

  template <typename T1, typename T2>
  static UPair<T2, T1> swap(const UPair<T1, T2> &p) {
    return UPair<T2, T1>{p.usnd, p.ufst};
  }

  template <typename T1, typename T2>
  static UPair<T1, T2> wrap_pair(T1 a, T2 b) {
    return UPair<T1, T2>{a, b};
  }

  template <typename A> struct UOption {
    // TYPES
    struct USome {
      A a0;
    };

    struct UNone {};

    using variant_t = std::variant<USome, UNone>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    UOption() {}

    explicit UOption(USome _v) : v_(std::move(_v)) {}

    explicit UOption(UNone _v) : v_(_v) {}

    template <typename _U> explicit UOption(const UOption<_U> &_other) {
      if (std::holds_alternative<typename UOption<_U>::USome>(_other.v())) {
        const auto &[a0] = std::get<typename UOption<_U>::USome>(_other.v());
        this->v_ = USome{[&]() -> A {
          if constexpr (std::is_same_v<_U, std::any>) {
            if (a0.type() == typeid(A))
              return std::any_cast<A>(a0);
            if constexpr (requires {
                            typename A::first_type;
                            typename A::second_type;
                          }) {
              const auto &[_k, _v] =
                  std::any_cast<std::pair<std::any, std::any>>(a0);
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
            return std::any_cast<A>(a0);
          } else
            return A(a0);
        }()};
      } else {
        this->v_ = UNone{};
      }
    }

    static UOption<A> usome(A a0) { return UOption(USome{std::move(a0)}); }

    static UOption<A> unone() { return UOption(UNone{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static T2 UOption_rect(F0 &&f, T2 f0, const UOption<T1> &u) {
    if (std::holds_alternative<typename UOption<T1>::USome>(u.v())) {
      const auto &[a0] = std::get<typename UOption<T1>::USome>(u.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static T2 UOption_rec(F0 &&f, T2 f0, const UOption<T1> &u) {
    if (std::holds_alternative<typename UOption<T1>::USome>(u.v())) {
      const auto &[a0] = std::get<typename UOption<T1>::USome>(u.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static UOption<T2> uoption_map(F0 &&f, const UOption<T1> &o) {
    if (std::holds_alternative<typename UOption<T1>::USome>(o.v())) {
      const auto &[a0] = std::get<typename UOption<T1>::USome>(o.v());
      return UOption<T2>::usome(f(a0));
    } else {
      return UOption<T2>::unone();
    }
  }

  static inline const uint64_t test_id_nat = poly_id<uint64_t>(UINT64_C(42));
  static inline const bool test_id_bool = poly_id<bool>(true);
  static inline const UPair<uint64_t, bool> test_pair =
      wrap_pair<uint64_t, bool>(UINT64_C(5), false);
  static inline const UPair<bool, uint64_t> test_swap =
      swap<uint64_t, bool>(test_pair);
  static inline const uint64_t test_fst = test_pair.ufst;
  static inline const bool test_snd = test_pair.usnd;
  static inline const UOption<uint64_t> test_umap =
      uoption_map<uint64_t, uint64_t>(
          [](uint64_t n) { return (n + UINT64_C(1)); },
          UOption<uint64_t>::usome(UINT64_C(9)));
};

#endif // INCLUDED_CONSTRAINED_POLY
