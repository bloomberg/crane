#include <closure_in_ctor.h>

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
ClosureInCtor::box ClosureInCtor::make_box_fix(unsigned int n) {
  auto add_impl = [=](auto &_self_add, unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return n;
    } else {
      unsigned int x_ = x - 1;
      return (_self_add(_self_add, x_) + 1);
    }
  };
  auto add = [=](unsigned int x) mutable -> unsigned int {
    return add_impl(add_impl, x);
  };
  return box::box0(add);
}
