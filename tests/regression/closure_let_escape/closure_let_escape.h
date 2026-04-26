#ifndef INCLUDED_CLOSURE_LET_ESCAPE
#define INCLUDED_CLOSURE_LET_ESCAPE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

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

struct ClosureLetEscape {
  /// A local fixpoint captures a LET-BINDING (not a function parameter)
  /// and escapes through Some (std::optional).
  ///
  /// BUG: Local fixpoints use & capture. The let-binding base is a
  /// stack variable. The fixpoint escapes through Some, so
  /// return_captures_by_value does NOT apply. After the function
  /// returns, base is destroyed, and the captured reference dangles.
  ///
  /// Difference from fix_escape_capture: captures a LET-BINDING
  /// (not a function parameter). The let-binding involves a computation
  /// (n * 2), so it can't be optimized away.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_fn_fix(const unsigned int &n);
  /// test1: make_fn_fix(21) => base=42, Some(add).
  /// add(3) = 42 + 3 = 45.
  /// Bug: & captures dangling reference to base.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = make_fn_fix(21u);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(3u);
    } else {
      return 999u;
    }
  }();
  /// test2: With noise between closure creation and invocation.
  /// base = 100, noise = 15, add(noise) = 100 + 15 = 115.
  static inline const unsigned int test2 = []() {
    std::optional<std::function<unsigned int(unsigned int)>> opt =
        make_fn_fix(50u);
    unsigned int noise = ((((1u + 2u) + 3u) + 4u) + 5u);
    if (opt.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *opt;
      return f(noise);
    } else {
      return 999u;
    }
  }();
  /// test3: Captures from multiple let bindings.
  /// BUG: Both a and b are captured by &, both dangle.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_fn_multi(const unsigned int &n);

  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_fn_multi(10u);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(5u);
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_CLOSURE_LET_ESCAPE
