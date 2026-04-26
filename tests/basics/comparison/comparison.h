#ifndef INCLUDED_COMPARISON
#define INCLUDED_COMPARISON

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

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

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
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
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
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
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
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

struct Comparison {
  enum class Cmp { e_CMPLT, e_CMPEQ, e_CMPGT };

  template <typename T1>
  static T1 cmp_rect(const T1 f, const T1 f0, const T1 f1, const Cmp c) {
    switch (c) {
    case Cmp::e_CMPLT: {
      return f;
    }
    case Cmp::e_CMPEQ: {
      return f0;
    }
    case Cmp::e_CMPGT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 cmp_rec(const T1 f, const T1 f0, const T1 f1, const Cmp c) {
    switch (c) {
    case Cmp::e_CMPLT: {
      return f;
    }
    case Cmp::e_CMPEQ: {
      return f0;
    }
    case Cmp::e_CMPGT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int cmp_to_nat(const Cmp c);
  __attribute__((pure)) static Cmp compare_nats(const unsigned int &a,
                                                const unsigned int &b);
  __attribute__((pure)) static unsigned int max_nat(unsigned int a,
                                                    unsigned int b);
  __attribute__((pure)) static unsigned int min_nat(unsigned int a,
                                                    unsigned int b);
  __attribute__((pure)) static unsigned int
  clamp(unsigned int val, unsigned int lo, unsigned int hi);
  __attribute__((pure)) static Cmp flip_cmp(const Cmp c);
  static inline const unsigned int test_lt_nat = cmp_to_nat(Cmp::e_CMPLT);
  static inline const unsigned int test_eq_nat = cmp_to_nat(Cmp::e_CMPEQ);
  static inline const unsigned int test_gt_nat = cmp_to_nat(Cmp::e_CMPGT);
  static inline const Cmp test_compare_lt = compare_nats(3u, 5u);
  static inline const Cmp test_compare_eq = compare_nats(5u, 5u);
  static inline const Cmp test_compare_gt = compare_nats(7u, 5u);
  static inline const unsigned int test_max = max_nat(3u, 7u);
  static inline const unsigned int test_min = min_nat(3u, 7u);
  static inline const unsigned int test_clamp_lo = clamp(1u, 3u, 7u);
  static inline const unsigned int test_clamp_mid = clamp(5u, 3u, 7u);
  static inline const unsigned int test_clamp_hi = clamp(9u, 3u, 7u);
  static inline const Cmp test_flip = flip_cmp(Cmp::e_CMPLT);
};

#endif // INCLUDED_COMPARISON
