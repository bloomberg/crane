#ifndef INCLUDED_FIX_ESCAPE_CAPTURE
#define INCLUDED_FIX_ESCAPE_CAPTURE

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

struct FixEscapeCapture {
  /// A local fixpoint that captures a function parameter and is returned
  /// in a pair. The fixpoint's & capture creates a dangling reference
  /// to the captured parameter after the enclosing function returns.
  __attribute__((pure)) static std::pair<
      unsigned int, std::function<unsigned int(unsigned int)>>
  make_pair_fn(unsigned int base);
  /// Invokes the escaped fixpoint — use-after-free if & capture.
  static inline const unsigned int test_pair = []() -> unsigned int {
    auto _cs = make_pair_fn(5u);
    const unsigned int &_x = _cs.first;
    const std::function<unsigned int(unsigned int)> &f = _cs.second;
    return f(3u);
  }();
  /// Same pattern with a non-recursive local fixpoint to isolate the
  /// capture issue from self-reference.
  __attribute__((pure)) static std::pair<
      unsigned int, std::function<unsigned int(unsigned int)>>
  make_pair_fn2(unsigned int base);

  static inline const unsigned int test_pair2 = []() -> unsigned int {
    auto _cs = make_pair_fn2(5u);
    const unsigned int &n = _cs.first;
    const std::function<unsigned int(unsigned int)> &f = _cs.second;
    return (n + f(3u));
  }();
};

#endif // INCLUDED_FIX_ESCAPE_CAPTURE
