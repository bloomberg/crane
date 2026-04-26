#ifndef INCLUDED_FIX_CAPTURE_FN_ARG
#define INCLUDED_FIX_CAPTURE_FN_ARG

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

struct FixCaptureFnArg {
  /// A local fixpoint captures a FUNCTION argument AND is returned
  /// through a pair (preventing uncurrying).
  ///
  /// BUG: go uses & capture. Both f (a std::function on the
  /// caller's stack) and base are captured by reference.
  /// The fixpoint escapes through the pair — after make_transform
  /// returns, f (the std::function object), base, and the local
  /// go are all destroyed. The returned closure dereferences a
  /// destroyed std::function when it calls f.
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static std::pair<
      unsigned int, std::function<unsigned int(unsigned int)>>
  make_transform(F0 &&f, unsigned int base) {
    auto go = std::make_shared<std::function<unsigned int(unsigned int)>>();
    *go = [=](unsigned int x) mutable -> unsigned int {
      if (x <= 0) {
        return f(base);
      } else {
        unsigned int x_ = x - 1;
        return ((*go)(x_) + 1);
      }
    };
    return std::make_pair(f(base), (*go));
  }

  /// test1: make_transform(x=>x*2, 5) = (10, go).
  /// go(3) = (5*2) + 3 = 13. Total = 10 + 13 = 23.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs =
        make_transform([](const unsigned int &x) { return (x * 2u); }, 5u);
    const unsigned int &n = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return (n + g(3u));
  }();
  /// test2: make_transform(S, 10) = (11, go).
  /// go(5) = S(10) + 5 = 16. Total = 11 + 16 = 27.
  static inline const unsigned int test2 = []() -> unsigned int {
    auto _cs = make_transform([](unsigned int x) { return (x + 1); }, 10u);
    const unsigned int &n = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return (n + g(5u));
  }();
};

#endif // INCLUDED_FIX_CAPTURE_FN_ARG
