#ifndef INCLUDED_FIX_CURRIED_ESCAPE
#define INCLUDED_FIX_CURRIED_ESCAPE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct FixCurriedEscape {
  /// A local fixpoint that escapes through an option wrapper,
  /// preventing Crane from uncurrying it away.
  ///
  /// make_fn defines a local fixpoint go with & capture of
  /// base (a stack variable).  Wrapping in Some forces
  /// the fixpoint to be stored as a std::function, because the
  /// return type option (nat -> nat) cannot be uncurried.
  ///
  /// BUG: The std::function holds & references to base.
  /// After make_fn returns, base is destroyed, and calling
  /// the extracted function accesses freed memory.
  __attribute__((
      pure)) static std::optional<std::function<unsigned int(unsigned int)>>
  make_fn(const unsigned int base);
  /// test1: unwrap and call — go captures base=42.
  /// go 3 = 42 + 3 = 45.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = make_fn(42u);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(3u);
    } else {
      return 999u;
    }
  }();
  /// test2: Different base to clobber the stack.
  /// make_fn 10 -> go captures base=10.
  /// go 7 = 10 + 7 = 17.
  static inline const unsigned int test2 = []() -> unsigned int {
    auto _cs = make_fn(10u);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(7u);
    } else {
      return 999u;
    }
  }();
  /// test3: Call make_fn twice — stack reuse should clobber base.
  /// First call returns go1 with base=100.
  /// Second call reuses the stack frame with base=0.
  /// If go1 reads the clobbered base, it returns 0+5=5 instead of 100+5=105.
  static inline const unsigned int test3 = []() {
    std::optional<std::function<unsigned int(unsigned int)>> fn1 =
        make_fn(100u);
    if (fn1.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *fn1;
      return f(5u);
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_FIX_CURRIED_ESCAPE
