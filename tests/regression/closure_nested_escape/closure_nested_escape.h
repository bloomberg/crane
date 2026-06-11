#ifndef INCLUDED_CLOSURE_NESTED_ESCAPE
#define INCLUDED_CLOSURE_NESTED_ESCAPE

#include <functional>
#include <utility>

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
  static std::pair<std::function<uint64_t(uint64_t)>,
                   std::function<uint64_t(uint64_t)>>
  make_pair_fix(uint64_t n);
  /// test1: make_pair_fix(5) returns (add, mul).
  /// add(3) = 5 + 3 = 8, mul(3) = 5 * 3 = 15.
  /// Expected: 8 + 15 = 23.
  static inline const uint64_t test1 = []() -> uint64_t {
    auto [f, g] = make_pair_fix(UINT64_C(5));
    return (f(UINT64_C(3)) + g(UINT64_C(3)));
  }();
  /// test2: With noise.
  /// add(0) = 7, mul(4) = 7 * 4 = 28.
  /// Expected: 7 + 28 = 35.
  static inline const uint64_t test2 = []() {
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = make_pair_fix(UINT64_C(7));
    return (p.first(UINT64_C(0)) + p.second(UINT64_C(4)));
  }();
  /// test3: Only use one of the two fixpoints.
  /// mul(10) where n=3 → 3*10 = 30.
  /// Expected: 30.
  static inline const uint64_t test3 = []() -> uint64_t {
    auto [_x, g] = make_pair_fix(UINT64_C(3));
    return g(UINT64_C(10));
  }();
};

#endif // INCLUDED_CLOSURE_NESTED_ESCAPE
