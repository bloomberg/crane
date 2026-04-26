#ifndef INCLUDED_MUTUAL_FIX_ESCAPE
#define INCLUDED_MUTUAL_FIX_ESCAPE

#include <functional>
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

struct MutualFixEscape {
  /// Mutual fixpoint using fix...with...for syntax, then return
  /// both functions through a pair.
  __attribute__((pure)) static std::pair<std::function<bool(unsigned int)>,
                                         std::function<bool(unsigned int)>>
  make_even_odd(const unsigned int &_x);
  /// test1: even(4) = true, odd(3) = true. 1+1=2.
  static inline const unsigned int test1 = []() {
    return []() -> unsigned int {
      auto _cs = make_even_odd(0u);
      const std::function<bool(unsigned int)> &ev = _cs.first;
      const std::function<bool(unsigned int)> &od = _cs.second;
      return ([&]() -> unsigned int {
        if (ev(4u)) {
          return 1u;
        } else {
          return 0u;
        }
      }() + [&]() -> unsigned int {
        if (od(3u)) {
          return 1u;
        } else {
          return 0u;
        }
      }());
    }();
  }();
  /// test2: even(5) = false, odd(6) = false. 0+0=0.
  static inline const unsigned int test2 = []() {
    return []() -> unsigned int {
      auto _cs = make_even_odd(0u);
      const std::function<bool(unsigned int)> &ev = _cs.first;
      const std::function<bool(unsigned int)> &od = _cs.second;
      return ([&]() -> unsigned int {
        if (ev(5u)) {
          return 1u;
        } else {
          return 0u;
        }
      }() + [&]() -> unsigned int {
        if (od(6u)) {
          return 1u;
        } else {
          return 0u;
        }
      }());
    }();
  }();
  /// A mutual fixpoint that captures a parameter base.
  __attribute__((
      pure)) static std::pair<std::function<unsigned int(unsigned int)>,
                              std::function<unsigned int(unsigned int)>>
  make_count_pair(unsigned int base);
  /// test3: count_even(0) = base = 10. count_odd(0) = 20.
  /// count_even(3) = 1+count_odd(2) = 1+(1+count_even(1))
  /// = 1+(1+(1+count_odd(0))) = 1+1+1+20 = 23.
  /// Total = 10 + 23 = 33.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_count_pair(10u);
    const std::function<unsigned int(unsigned int)> &ce = _cs.first;
    const std::function<unsigned int(unsigned int)> &_x = _cs.second;
    return (ce(0u) + ce(3u));
  }();
  /// test4: with noise. count_odd(1) = 1+count_even(0) = 1+5 = 6.
  static inline const unsigned int test4 = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = make_count_pair(5u);
    return p.second(1u);
  }();
};

#endif // INCLUDED_MUTUAL_FIX_ESCAPE
