#ifndef INCLUDED_FIX_PAIR_TWO_CLOSURES
#define INCLUDED_FIX_PAIR_TWO_CLOSURES

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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct FixPairTwoClosures {
  /// Two local fixpoints escape through a pair.
  ///
  /// BUG: Both f and g use & capture. They capture a, b,
  /// and each other's std::function variables. All captured references
  /// dangle after make_ops returns.
  __attribute__((
      pure)) static std::pair<std::function<unsigned int(unsigned int)>,
                              std::function<unsigned int(unsigned int)>>
  make_ops(unsigned int a, unsigned int b);
  /// test1: make_ops(10, 20). fst(3) = 10+3 = 13, snd(5) = 20+5 = 25.
  /// Total = 38.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = make_ops(10u, 20u);
    const std::function<unsigned int(unsigned int)> &f = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return (f(3u) + g(5u));
  }();
  /// test2: Use both closures interleaved.
  /// fst(1) + snd(2) + fst(3) = 11 + 22 + 13 = 46.
  static inline const unsigned int test2 = []() -> unsigned int {
    auto _cs = make_ops(10u, 20u);
    const std::function<unsigned int(unsigned int)> &f = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return ((f(1u) + g(2u)) + f(3u));
  }();
  /// test3: Asymmetric arguments to stress different captured values.
  /// make_ops(100, 1). fst(0) + snd(0) = 100 + 1 = 101.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_ops(100u, 1u);
    const std::function<unsigned int(unsigned int)> &f = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return (f(0u) + g(0u));
  }();
};

#endif // INCLUDED_FIX_PAIR_TWO_CLOSURES
