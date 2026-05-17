#ifndef INCLUDED_CONSTRAINED_POLY
#define INCLUDED_CONSTRAINED_POLY

#include <type_traits>
#include <utility>
#include <variant>

struct ConstrainedPoly {
  template <typename T1> static T1 poly_id(T1 x) { return x; }

  template <typename A, typename B> struct UPair {
    A ufst;
    B usnd;

    // ACCESSORS
    UPair<A, B> clone() const {
      return UPair<A, B>{(*this).ufst, (*this).usnd};
    }
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

    UOption(const UOption<A> &_other) : v_(_other.v_) {}

    UOption(UOption<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    UOption<A> &operator=(const UOption<A> &_other) {
      v_ = _other.v_;
      return *this;
    }

    UOption<A> &operator=(UOption<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    UOption<A> clone() const {
      if (std::holds_alternative<USome>(this->v())) {
        const auto &[a0] = std::get<USome>(this->v());
        return UOption<A>(USome{a0});
      } else {
        return UOption<A>(UNone{});
      }
    }

    // CREATORS
    template <typename _U> explicit UOption(const UOption<_U> &_other) {
      if (std::holds_alternative<typename UOption<_U>::USome>(_other.v())) {
        const auto &[a0] = std::get<typename UOption<_U>::USome>(_other.v());
        this->v_ = USome{A(a0)};
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

  static inline const unsigned int test_id_nat = poly_id<unsigned int>(42u);
  static inline const bool test_id_bool = poly_id<bool>(true);
  static inline const UPair<unsigned int, bool> test_pair =
      wrap_pair<unsigned int, bool>(5u, false);
  static inline const UPair<bool, unsigned int> test_swap =
      swap<unsigned int, bool>(test_pair);
  static inline const unsigned int test_fst = test_pair.ufst;
  static inline const bool test_snd = test_pair.usnd;
  static inline const UOption<unsigned int> test_umap =
      uoption_map<unsigned int, unsigned int>(
          [](unsigned int n) { return (n + 1u); },
          UOption<unsigned int>::usome(9u));
};

#endif // INCLUDED_CONSTRAINED_POLY
