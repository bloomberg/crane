#include <closure_in_ctor.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// A local fixpoint captures the function parameter n and is stored
/// in Box — a user-defined inductive (not option, not pair).
///
/// BUG: Local fixpoints generate std::function with & capture
/// (needed for self-reference). This & also captures n by reference.
/// The fixpoint escapes through Box, so return_captures_by_value
/// does NOT apply. After make_box_fix returns, n is destroyed,
/// and the captured reference dangles.
///
/// Difference from fix_escape_capture: escapes through a CUSTOM
/// INDUCTIVE constructor, not a pair.
std::shared_ptr<ClosureInCtor::box>
ClosureInCtor::make_box_fix(const unsigned int n) {
  std::function<unsigned int(unsigned int)> add;
  add = [&](unsigned int x) -> unsigned int {
    if (x <= 0) {
      return n;
    } else {
      unsigned int x_ = x - 1;
      return (add(x_) + 1);
    }
  };
  return box::box0(add);
}
