#ifndef INCLUDED_CLOSURE_NESTED_ESCAPE
#define INCLUDED_CLOSURE_NESTED_ESCAPE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ClosureNestedEscape {
  /// A function takes a nat and returns a PAIR of fixpoints, both
  /// capturing the same parameter.
  ///
  /// BUG: Both fixpoints use & capture. They capture n by reference.
  /// Both are stored in a pair (constructor), so return_captures_by_value
  /// does NOT apply. After the function returns, n dangles.
  ///
  /// Difference from fix_escape_capture: returns TWO fixpoints that both
  /// capture the SAME variable. This tests whether both closures
  /// independently read garbage from the same dangling reference.
  __attribute__((
      pure)) static std::pair<std::function<unsigned int(unsigned int)>,
                              std::function<unsigned int(unsigned int)>>
  make_pair_fix(const unsigned int n);
  /// test1: make_pair_fix(5) returns (add, mul).
  /// add(3) = 5 + 3 = 8, mul(3) = 5 * 3 = 15.
  /// Expected: 8 + 15 = 23.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = make_pair_fix(5u);
    const std::function<unsigned int(unsigned int)> &f = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return (f(3u) + g(3u));
  }();
  /// test2: With noise.
  /// add(0) = 7, mul(4) = 7 * 4 = 28.
  /// Expected: 7 + 28 = 35.
  static inline const unsigned int test2 = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = make_pair_fix(7u);
    return (p.first(0u) + p.second(4u));
  }();
  /// test3: Only use one of the two fixpoints.
  /// mul(10) where n=3 → 3*10 = 30.
  /// Expected: 30.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_pair_fix(3u);
    const std::function<unsigned int(unsigned int)> &_x = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return g(10u);
  }();
};

#endif // INCLUDED_CLOSURE_NESTED_ESCAPE
