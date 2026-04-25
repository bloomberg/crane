#ifndef INCLUDED_CONSTRAINED_POLY
#define INCLUDED_CONSTRAINED_POLY

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

struct ConstrainedPoly {
  template <typename T1> static T1 poly_id(const T1 x) { return x; }

  template <typename t_A, typename t_B> struct UPair {
    t_A ufst;
    t_B usnd;

    __attribute__((pure)) UPair<t_A, t_B> *operator->() { return this; }

    __attribute__((pure)) const UPair<t_A, t_B> *operator->() const {
      return this;
    }
  };

  template <typename T1, typename T2>
  constexpr static UPair<T2, T1> swap(const UPair<T1, T2> &p) {
    return UPair<T2, T1>{p.usnd, p.ufst};
  }

  template <typename T1, typename T2>
  __attribute__((pure)) static UPair<T1, T2> wrap_pair(const T1 a, const T2 b) {
    return UPair<T1, T2>{a, b};
  }

  template <typename t_A> struct UOption {
    // TYPES
    struct USome {
      t_A d_a0;
    };

    struct UNone {};

    using variant_t = std::variant<USome, UNone>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    UOption() {}

    explicit UOption(USome _v) : d_v_(std::move(_v)) {}

    explicit UOption(UNone _v) : d_v_(_v) {}

    UOption(const UOption<t_A> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    UOption(UOption<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) UOption<t_A> &operator=(const UOption<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) UOption<t_A> &operator=(UOption<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) UOption<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<USome>(_sv.v())) {
        const auto &[d_a0] = std::get<USome>(_sv.v());
        return UOption<t_A>(USome{clone_as_value<t_A>(d_a0)});
      } else {
        return UOption<t_A>(UNone{});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) UOption<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<USome>(_sv.v())) {
        const auto &[d_a0] = std::get<USome>(_sv.v());
        return UOption<_CloneT0>(
            typename UOption<_CloneT0>::USome{clone_as_value<_CloneT0>(d_a0)});
      } else {
        return UOption<_CloneT0>(typename UOption<_CloneT0>::UNone{});
      }
    }

    // CREATORS
    __attribute__((pure)) static UOption<t_A> usome(t_A a0) {
      return UOption(USome{std::move(a0)});
    }

    constexpr static UOption<t_A> unone() { return UOption(UNone{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) UOption<t_A> *operator->() { return this; }

    __attribute__((pure)) const UOption<t_A> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = UOption<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 UOption_rect(F0 &&f, const T2 f0, const UOption<T1> &u) {
    if (std::holds_alternative<typename UOption<T1>::USome>(u.v())) {
      const auto &[d_a0] = std::get<typename UOption<T1>::USome>(u.v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 UOption_rec(F0 &&f, const T2 f0, const UOption<T1> &u) {
    if (std::holds_alternative<typename UOption<T1>::USome>(u.v())) {
      const auto &[d_a0] = std::get<typename UOption<T1>::USome>(u.v());
      return f(d_a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static UOption<T2> uoption_map(F0 &&f,
                                                       const UOption<T1> &o) {
    if (std::holds_alternative<typename UOption<T1>::USome>(o.v())) {
      const auto &[d_a0] = std::get<typename UOption<T1>::USome>(o.v());
      return UOption<T2>::usome(f(d_a0));
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
          [](const unsigned int &n) { return (n + 1u); },
          UOption<unsigned int>::usome(9u));
};

#endif // INCLUDED_CONSTRAINED_POLY
