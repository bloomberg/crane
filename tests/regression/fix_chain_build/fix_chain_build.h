#ifndef INCLUDED_FIX_CHAIN_BUILD
#define INCLUDED_FIX_CHAIN_BUILD

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

struct FixChainBuild {
  /// Recursive construction of a closure chain. Each level creates a
  /// local fixpoint that captures the current n AND the previous
  /// level's closure prev, then stores the fixpoint in a pair with
  /// its base value (preventing uncurrying).
  ///
  /// BUG: Each step fixpoint uses & capture, binding n (the
  /// current stack frame's parameter), prev (a local variable),
  /// and step itself. When build_chain returns, the stack frame
  /// is destroyed, and the returned closure holds dangling references.
  __attribute__((pure)) static std::pair<
      unsigned int, std::function<unsigned int(unsigned int)>>
  build_chain(unsigned int n);
  /// test1: build_chain(1) = (1, step1).
  /// step1(0) = 1.
  /// step1(2) = S(prev(step1(1))) = S(prev(S(prev(step1(0)))))
  /// = S(prev(S(prev(1)))) = S(prev(S(1))) = S(prev(2)) = S(2) = 3.
  /// Pair first + step1(2) = 1 + 3 = 4.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = build_chain(1u);
    const unsigned int &base = _cs.first;
    const std::function<unsigned int(unsigned int)> &f = _cs.second;
    return (base + f(2u));
  }();
  /// test2: build_chain(2).
  /// step1 captures prev=id, n=1. step2 captures prev=step1, n=2.
  /// step2(0) = 2. Result: 2 + step2(0) = 2 + 2 = 4.
  static inline const unsigned int test2 = []() -> unsigned int {
    auto _cs = build_chain(2u);
    const unsigned int &base = _cs.first;
    const std::function<unsigned int(unsigned int)> &f = _cs.second;
    return (base + f(0u));
  }();
  /// test3: build_chain(3). More nesting = more dangling frames.
  /// step3(0) = 3. Result: 3 + 3 = 6.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = build_chain(3u);
    const unsigned int &base = _cs.first;
    const std::function<unsigned int(unsigned int)> &f = _cs.second;
    return (base + f(0u));
  }();
};

#endif // INCLUDED_FIX_CHAIN_BUILD
