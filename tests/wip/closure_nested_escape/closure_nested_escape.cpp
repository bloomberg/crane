#include <closure_nested_escape.h>

#include <functional>
#include <type_traits>
#include <utility>

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
__attribute__((pure)) std::pair<std::function<unsigned int(unsigned int)>,
                                std::function<unsigned int(unsigned int)>>
ClosureNestedEscape::make_pair_fix(const unsigned int n) {
  std::function<unsigned int(unsigned int)> add;
  add = [&](unsigned int x) -> unsigned int {
    if (x <= 0) {
      return n;
    } else {
      unsigned int x_ = x - 1;
      return (add(x_) + 1);
    }
  };
  std::function<unsigned int(unsigned int)> mul;
  mul = [&](unsigned int x) -> unsigned int {
    if (x <= 0) {
      return 0u;
    } else {
      unsigned int x_ = x - 1;
      return (n + mul(x_));
    }
  };
  return std::make_pair(add, mul);
}
